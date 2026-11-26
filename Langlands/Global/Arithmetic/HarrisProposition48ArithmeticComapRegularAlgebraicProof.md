# Arithmetic pullback of regular algebraicity for the singleton child

`Langlands.Global.Harris.arithmeticComapRegularAlgebraic` proves exactly
`Langlands.Global.Harris.ArithmeticComapRegularAlgebraicStatement` of
`Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement`, at
independent universe levels `uK` and `uE` of the two number fields. For number
fields `K` and `E` with compact adele quotients, an isomorphism
`e : K ≃+* E`, a rank index `r` and an actual irreducible cuspidal realization
`S` over `E` of rank `r + 1`, regular algebraicity of `S.isoClass` gives
regular algebraicity of `(S.arithmeticComap e).isoClass`.

## Implemented proof

The proof applies
`Langlands.Automorphic.CuspidalOperatorRealization.arithmeticComap_isoClass_isRegularAlgebraic_iff`
of `Langlands.Automorphic.RegularAlgebraicArithmeticTransport` in the forward
direction. That module carries the actual infinitesimal character along the
arithmetic transports of the archimedean data:

1. `embeddingIndexEquiv e` reindexes the embedding indices of `E` by those of
   `K` over the pulled-back places. The two indices of a complex place are
   exchanged when the chosen embedding of the pulled-back place is the
   conjugate of the composite with `e`. The arithmetic transport
   `mixedEquiv e` of `K ⊗ ℝ` permutes the embedding coordinates accordingly
   (`embeddingComponent_mixedEquiv`, by density of `K` in `K ⊗ ℝ`).
2. The enveloping algebra isomorphism `envelopingEquiv n e` sends the
   complexified real diagonal and matrix-unit generators of `K` to those of
   `E`, and diagonal weights are reindexed along `embeddingIndexEquiv e`
   (`envelopingEquiv_realGenerator`, `diagonalWeight_mixedEquiv`).
3. A highest-weight vector `w` of weight `μ` for `E` gives the class of `1` in
   the cyclic quotient of the enveloping algebra of `K` by the left ideal
   `{a | envelopingEquiv n e a • w = 0}`. This module lies in the universe of
   `K`, and its vector has the reindexed weight. Hence
   `χ ∘ centerEquiv n e` is regular algebraic when `χ` is, with the same
   dominance and integrality (`isRegularAlgebraicCharacter_comp_centerEquiv`).
4. `arithmeticComapEquiv_differential` intertwines the differential actions
   on `S` and on its pullback along `envelopingEquiv n e`, so the pullback
   has infinitesimal character `χ ∘ centerEquiv n e`
   (`OperatorRealization.HasInfinitesimalCharacter.arithmeticComap`).

## Context

The Markdown of
`Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement`
describes the use: the regularity property of the singleton child in the proof
of Harris 1998, Proposition 4.8 (M. Harris, *The local Langlands conjecture
for GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210,
pp. 202–203), pulled back along an isomorphism of the child's field with the
step field in the inverse direction. The regular algebraic predicate is
Clozel's (1990, Définitions 1.8 and 3.12) in the formulation of
`Langlands.Automorphic.RegularAlgebraic`.
