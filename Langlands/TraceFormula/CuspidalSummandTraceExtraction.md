# A cuspidal summand carrying a nonzero trace

Let `R(f)` be the operator of an integrable function `f` on the adelic points of a connected
reductive group, acting on `L²` of the positive rational quotient, and let `S` be the actual
almost-everywhere cuspidal subspace.

`cuspidalCompression_eq_of_range` shows that when `R(f)` maps all of `L²` into `S`, its
compression `P_S ∘ R(f) ∘ ι_S` to `S` is the cuspidal integrated action
`fullAEL2CuspidalIntegratedAction`.

`exists_irreducibleSummand_compressedTrace_ne_zero` assumes that the cuspidal integrated
actions of compactly supported continuous functions are compact, and that `R(f)` is trace
class, maps into `S` and has nonzero trace. It produces a nonzero closed invariant subspace
`P` of `S` with no closed invariant subspaces other than `0` and `P`, such that the
compression of `R_S(f)` to `P` is trace class with nonzero trace.

The proof applies `hilbertSumTrace` twice. Its first part shows that the compression of a
trace-class operator with range in `S` is trace class with the same trace; by
`cuspidalCompression_eq_of_range` this compression is `R_S(f)`. The compactness hypothesis
gives, through `groupSchemeFullAEL2CuspidalDecomposition`, an orthogonal Hilbert sum
decomposition of `S` into irreducible closed invariant subspaces. The second part of
`hilbertSumTrace` writes the trace of `R_S(f)` as the sum of the traces of its compressions to
the summands, each trace class. If all these traces vanished, the sum and hence the trace of
`R(f)` would be zero.
