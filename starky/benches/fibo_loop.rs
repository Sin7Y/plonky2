use core::marker::PhantomData;
use std::time::Instant;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use log::{info, LevelFilter};
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::Field;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2::util::timing::TimingTree;
use starky::config::StarkConfig;
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use starky::permutation::PermutationPair;
use starky::prover::prove;
use starky::stark::Stark;
use starky::util::trace_rows_to_poly_values;
use starky::vars::{StarkEvaluationTargets, StarkEvaluationVars};
use starky::verifier::verify_stark_proof;

const COLUMNS: usize = 2;
const PUBLIC_INPUTS: usize = 2;
/// Toy STARK system used for testing.
/// Computes a Fibonacci sequence with state `[x0, x1, i, j]` using the state transition
/// `x0' <- x1, x1' <- x0 + x1, i' <- i+1, j' <- j+1`.
/// x0` = x0+x1, x1`=x1+x0`
/// Note: The `i, j` columns are only used to test the permutation argument.
#[derive(Copy, Clone)]
struct FibonacciStark<F: RichField + Extendable<D>, const D: usize> {
    num_rows: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> FibonacciStark<F, D> {
    // The first public input is `x0`.
    const PI_INDEX_X0: usize = 0;
    // The second public input is `x1`.
    const PI_INDEX_X1: usize = 1;
    // The third public input is the second element of the last row, which should be equal to the
    // `num_rows`-th Fibonacci number.
    // const PI_INDEX_RES: usize = 2;

    fn new(num_rows: usize) -> Self {
        Self {
            num_rows,
            _phantom: PhantomData,
        }
    }

    /// Generate the trace using `x0, x1, 0, 1` as initial state values.
    fn generate_trace(&self, x0: F, x1: F) -> Vec<PolynomialValues<F>> {
        let mut trace_rows = (0..self.num_rows)
            .scan([x0, x1], |acc, _| {
                let tmp = *acc;
                acc[0] = tmp[0] + tmp[1];
                acc[1] = acc[0] + tmp[1];
                Some(tmp)
            })
            .collect::<Vec<_>>();
        trace_rows_to_poly_values(trace_rows)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FibonacciStark<F, D> {
    const COLUMNS: usize = 2;
    const PUBLIC_INPUTS: usize = 2;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, { COLUMNS }, { PUBLIC_INPUTS }>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        // Check public inputs.
        yield_constr
            .constraint_first_row(vars.local_values[0] - vars.public_inputs[Self::PI_INDEX_X0]);
        yield_constr
            .constraint_first_row(vars.local_values[1] - vars.public_inputs[Self::PI_INDEX_X1]);
        // yield_constr
        //     .constraint_last_row(vars.local_values[1] - vars.public_inputs[Self::PI_INDEX_RES]);

        // x0' <- x1 + x0
        yield_constr.constraint_transition(
            vars.next_values[0] - vars.local_values[1] - vars.local_values[0],
        );
        // x1' <- x0` + x1
        yield_constr.constraint_transition(
            vars.next_values[1] - vars.next_values[0] - vars.local_values[1],
        );
    }

    // 0 1
    // 1 2
    // 3 5
    // 8 13
    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { COLUMNS }, { PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        // Check public inputs.
        let pis_constraints = [
            builder.sub_extension(vars.local_values[0], vars.public_inputs[Self::PI_INDEX_X0]),
            builder.sub_extension(vars.local_values[1], vars.public_inputs[Self::PI_INDEX_X1]),
            // builder.sub_extension(vars.local_values[1], vars.public_inputs[Self::PI_INDEX_RES]),
        ];
        yield_constr.constraint_first_row(builder, pis_constraints[0]);
        yield_constr.constraint_first_row(builder, pis_constraints[1]);
        // yield_constr.constraint_last_row(builder, pis_constraints[1]);

        // x0' <- x1
        let first_col_constraint = builder.sub_extension(vars.next_values[0], vars.local_values[1]);
        yield_constr.constraint_transition(builder, first_col_constraint);
        // x1' <- x0 + x1
        let second_col_constraint = {
            let tmp = builder.sub_extension(vars.next_values[1], vars.local_values[0]);
            builder.sub_extension(tmp, vars.local_values[1])
        };
        yield_constr.constraint_transition(builder, second_col_constraint);
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        // vec![PermutationPair::singletons(2, 3)]
        vec![]
    }
}

fn fibonacci<F: Field>(n: usize, x0: F, x1: F) -> F {
    (0..n).fold((x0, x1), |x, _| (x.1, x.0 + x.1)).1
}

fn test_fibonacci_stark() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = FibonacciStark<F, D>;

    let config = StarkConfig::standard_fast_config();
    let num_rows = 1 << 20;
    let public_inputs = [F::ZERO, F::ONE];

    // let public_inputs = [F::ZERO, F::ONE, fibonacci(num_rows - 1, F::ZERO, F::ONE)];
    let stark = S::new(num_rows);
    let trace = stark.generate_trace(public_inputs[0], public_inputs[1]);
    info!("exec step:{}", trace[0].len());
    // let start = Instant::now();
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace,
        public_inputs,
        &mut TimingTree::default(),
    );

    // let exec_time = start.elapsed();
    // info!(
    //     "exec_time: {}, exec res ok:{}",
    //     exec_time.as_millis(),proof.is_ok()
    // );
    // let res = verify_stark_proof(stark, proof.unwrap(), &config);
    // println!("res:{:?}", res);
}

fn fibo_loop_benchmark(c: &mut Criterion) {
    let _ = env_logger::builder()
        .filter_level(LevelFilter::Info)
        .try_init();

    let mut group = c.benchmark_group("fibo_loop");

    for inst_size in [0x6000] {
        group.bench_with_input(
            BenchmarkId::from_parameter(inst_size),
            &inst_size,
            |b, p| {
                b.iter(|| {
                    test_fibonacci_stark();
                });
            },
        );
    }
}

criterion_group![
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = fibo_loop_benchmark
];
criterion_main!(benches);
