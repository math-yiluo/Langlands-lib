# The torus filtration of quasi-split building data over `K = F^ur`

Module `Langlands.Geometry.Building.KPQuasiSplitLocalTorusFiltrationProof`.
The theorem `Langlands.Geometry.Building.quasiSplitLocalTorusFiltration` proves exactly
`QuasiSplitLocalTorusFiltrationStatement.{u}` at arbitrary universe `u`.

The statement retains every published hypothesis: a nonarchimedean local field `F` of
any characteristic, `K = UnramifiedClosure F`, an affine group scheme `H` over `Spec K`,
supplied `B : MaximalUnramified.BuildingData F H`, and
`hZ : IsTorus B.centralizer.Z`. It uses the published definitions
`Z(K)_r = B.centralizerTorusFiltration hZ r` and
`j(Z(K)_r) = B.centralizerTorusImage hZ r` from `KPLocalMoyPrasadGroups`.

## Implemented proof

The proof applies `quasiSplitLocalTorusFiltration_of_coroot_of_torusRoot` from the
supporting module `KPLocalCentralizerTorusFiltrationClauses` to the two published
theorems `kpLocalCorootComponent` and `kpLocalTorusRootCommutator`. These prove
`KPLocalCorootComponentStatement.{u}` and `KPLocalTorusRootCommutatorStatement.{u}`,
respectively, with no added premise. The helper introduces the statement's data
and assembles its three conjuncts as follows.

1. **Commutator friendliness.**
   `B.centralizerTorusFiltration_isCommutatorFriendly_of_coroot` in
   `KPLocalCentralizerFiltrationCommutatorFriendly` applies `kpLocalCorootComponent`.
   For every factorization of the specified opposite-root commutator, its centralizer
   component is the image of a point `c` of an induced torus. Every geometric character
   of `c` satisfies the required positive-depth congruence bound.
   `mem_localTorusFiltration_of_induced` turns that bound into filtration membership;
   `map_localTorusFiltration_le` transports it to `Z(K)_r`.
2. **Root compatibility, including depth zero.**
   `B.centralizerTorusImage_isRootCompatible_of_torusRoot` in
   `KPLocalCentralizerFiltrationRootCompatible` writes the given element as `j(t)`.
   At positive depth, `localTorusFiltration_le_localGeometricCharacterCongruence`
   supplies the hypothesis of `kpLocalTorusRootCommutator`. Its conclusion is the
   exact block `U_{a,x,r+s} · U_{2a,x,r+s}`.
   At depth zero, D1's
   `centralizerTorusFiltration_le_characterValuationKernel` and
   `characterValuationKernel_eq_of_isEquiv (valuation_isEquiv F)` place `t` in the
   apartment valuation's character kernel. The apartment compatibility theorem
   `B.isOmegaCompatible.smul_eq_self`, the conjugation rule
   `B.apartment.conj_mem_filtration`, and
   `weylAction_centralizerToNormalizer` show that `j(t)` preserves `U_{a,x,s}`.
   The commutator therefore belongs to that subgroup and gives the first block
   factor; the second factor is `1`.
3. **Normalizer stability.**
   `B.centralizerTorusImage_isNormalizerStable` is imported from the published module
   `KPLocalCentralizerFiltrationNormalizerStable`. That theorem restricts conjugation
   by a normalizer point to an automorphism of the centralizer torus, applies
   `map_localTorusFiltration_le`, and applies the same inclusion to the inverse
   normalizer point to obtain equality.

The result covers multipliable and divisible roots and all nonnegative depths in
the second and third clauses. No characteristic restriction or further building,
coordinate, or filtration hypothesis is introduced. The statement pair and all
its imported pairs are unchanged.

## Provenance and authorship

This is an internal composition of Library results and the three supporting
helper modules submitted with it. The literal commutator-friendly assertion is
KP Lemma 7.2.3; root compatibility and normalizer stability are the additional
derived clauses of the published target. Its source scope and the distinction
are documented in `KPQuasiSplitLocalTorusFiltrationStatement.md`. The final
composition cites no additional literature.

Worker 119 supplied the three helper modules. Their Lean proofs are reused
unchanged from that worker's shared draft; Worker 228 assembled the exact
unconditional theorem and prepared this proof contribution.
