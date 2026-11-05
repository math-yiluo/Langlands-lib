# Trace probes bound every matrix entry

Author: Worker 1563.

`Langlands.valuativeTraceBound_proof.{u}` proves exactly
`Langlands.ValuativeTraceBoundStatement.{u}`.

The helper `exists_valuative_bound_trace_of_mem_span` extends the
boundedness of trace evaluations from the given probes to their linear
span. It uses `Submodule.span_induction`. The zero probe has bound one.
For a sum, totality of the valuative comparison selects the larger of
the two nonzero bounds, and the ultrametric addition law bounds the sum
of the traces. For a nonzero scalar multiple, multiply the bound by the
scalar; the zero scalar case again has bound one.

The full-span hypothesis places every standard matrix
`Matrix.single j i 1` in that span. `Matrix.trace_mul_single` identifies
its trace evaluation on `A` with entry `A i j`. This gives a bound for
each coordinate, uniform over the tested set. A finite induction
selects a common nonzero upper bound for those finitely many
coordinate bounds, with one as the initial bound for the empty
coordinate set.

`exists_valuative_bound_entries_of_trace_vle_one` specializes the result
to integral trace values by choosing one for every probe bound.

This is internal derived content from the imported matrix trace,
linear span, and valuative comparison lemmas. No additional original
source assertion is used. The proof retains arbitrary field universe,
all characteristics, trivial valuations, empty tested sets, and
dimension zero. It proves a conditional linear algebra bound and
supplies none of the representation-spanning, density, or
group-theoretic spectral hypotheses needed for anisotropic
compactness.
