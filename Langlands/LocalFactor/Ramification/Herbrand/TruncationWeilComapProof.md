# Weil upper groups through the transitivity index

`Langlands.Ramification.Kummer.truncationWeilComap` proves
`TruncationWeilComapStatement.{u}`. If the absolute upper group of `F` at
`μ` acts transitively on the `F`-embeddings of the finite intermediate
extension `E`, the preimage of the Weil upper group of `F` at `x` under
`intermediateWeilMap F E` is the Weil upper group of `E` at `x`, for
`-1 ≤ x ≤ μ`.

The proof applies `herbrandPsiTruncation` to the transitivity hypothesis
and both bounds on `x` to obtain `relativeHerbrandPsi E x = x`. By
`Subgroup.ext` and `Subgroup.mem_comap`, it suffices to compare membership
for each element `w` of the Weil group of `E`. The published comparison
`HerbrandBridge.intermediateWeilMap_mem_upperGroup_iff` equates membership
of the image of `w` at index `x` over `F` with membership of `w` at index
`relativeHerbrandPsi E x` over `E`. Rewriting that index gives the desired
equivalence, including at `x = -1` and `x = μ`.

This is the subgroup-intersection step of Lemma `lem:trunc` in the operator
route note `operator-numerical-llc-route-2026-11-16`, lines 876–888. The
[statement's documentation](TruncationQuotientStatement.md) explains the
formulation over the interval `[-1, μ]`.
