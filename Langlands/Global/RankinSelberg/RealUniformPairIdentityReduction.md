# The real-place functional equation from Jacquet's pair identity

Intermediate result towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

The module reduces `RealPlaceFunctionalEquationStatement` to three premises:
- Jacquet's pair identity for the real unequal-rank local integrals on the uniform coefficient
  spaces;
- the same identity for the real positive equal-rank local integrals;
- the Library's `RealPlaceContragredientPairLStatement` (real-place contragredient pair-factor
  denominator compatibility).

It combines `realPairIdentityContinuation` (module `ArchimedeanRealPairIdentity`) with the
convergence theorems `realUnequalPairConvergence` and `realEqualPairConvergence`, the
regularity theorem `realUniformWhittakerRegularity`, and the reduction
`realPlaceUniformContinuationReduction` (module `RealUniformContinuationReduction`).

## The statements

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal`.

**`RealLocalUniformUnequalPairIdentityStatement : Prop`.** It has the same quantifiers as
`RealLocalUniformUnequalContinuationStatement`:
- ranks `r t : ℕ` with `h : t < r`, block lists `ds, es` with `realRank ds = r + 1` and
  `realRank es = t + 1`;
- `a : ℝˣ`, quotient measure data `D : RealQuotientMeasureData t`;
- `W ∈ realUniformWhittakerModel r ds a` and `W' ∈ realUniformWhittakerModel t es (-a)`.

Its conclusion is
`UnequalPairIdentity h a D W W' ds es dds ees (-a) sign`, with
`dds = ds.map RealLocalJacquet.dualBlock`, `ees = es.map RealLocalJacquet.dualBlock` and
`sign = det_ds(-1)^(t+1) · det_es(-1)`, where `det_ds = RealJacquet.determinant ds`. These are
the same block lists, epsilon parameter `-a` and sign as in the continuation statement.

**`RealLocalUniformPositiveEqualPairIdentityStatement : Prop`.** It has the same quantifiers as
`RealLocalUniformPositiveEqualContinuationStatement`:
- `r : ℕ` with `0 < r`, block lists `ds, es` of rank `r + 1`;
- `a : ℝˣ`, `D : RealQuotientMeasureData r`;
- `W ∈ realUniformWhittakerModel r ds a`, `W' ∈ realUniformWhittakerModel r es (-a)`, and a
  Schwartz function `Φ` on `ℝ^(r+1)`.

Its conclusion is `EqualPairIdentity a (-a) D W W' Φ ds es dds ees sign`, with
`sign = det_ds(-1)^r`.

`UnequalPairIdentity` and `EqualPairIdentity` (module `ArchimedeanRealPairIdentity`) state
Jacquet's identity:
`∫ K(0)(q) h(|det g|) dq = ∫ Kd(0)(p) k(|det g|) dp`.
Here `K`, `Kd` are the Library's real local Rankin–Selberg kernels at `s = 0`. The identity is
required for every measurable, rapidly decreasing pair `(h, k)` on `(0, ∞)` satisfying, for
some real `B`,
- `mellin h (-s) = sign · ε(s) · exp(s² + B s) / L(s)`;
- `mellin k (s - 1) = exp(s² + B s) / Ld(1 - s)`.

Here `L`, `Ld` and `ε` are the factors of `RealJacquet.UnequalEquation` and
`RealJacquet.EqualEquation`. In Lean the reciprocals are written with the entire
denominators of `realPairLFactor`.

**`RealPlacePairIdentityReductionStatement.{u} : Prop`** is the implication

`RealLocalUniformUnequalPairIdentityStatement → RealLocalUniformPositiveEqualPairIdentityStatement → RealPlaceContragredientPairLStatement.{u} → RealPlaceFunctionalEquationStatement.{u}`.

The theorem `realPlacePairIdentityReduction` proves it.

## Proof

- `realLocalUniformUnequalContinuation_of_pairIdentity`: the unequal-rank pair-identity
  statement implies `RealLocalUniformUnequalContinuationStatement`. For given data:
  - `realUniformWhittakerRegularity` gives the regularity and growth of `W` (for `a`) and of
    `W'` (for `-a`);
  - `realUnequalPairConvergence` then gives `σ₀` such that both unequal-rank kernels are
    integrable for `Re s > σ₀`;
  - the sign is nonzero, since `RealJacquet.determinant` takes values in `ℂˣ`;
  - the unequal part of `realPairIdentityContinuation`, applied with these hypotheses and the
    pair identity, gives the conclusion of `RealJacquet.UnequalContinuation`.
- `realLocalUniformPositiveEqualContinuation_of_pairIdentity`: the same argument in equal rank,
  with `realEqualPairConvergence` and the equal part of `realPairIdentityContinuation`.
- `realPlacePairIdentityReduction`: these two implications, followed by
  `realPlaceUniformContinuationReduction`.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009):
- §8.1, pp. 53–54, is the source of the pair-identity method. For principal series Jacquet
  states that the assertions of Theorem 2.1 for the equal pair `(n, n)` are equivalent to the
  identity of the two integrals `Ψ(θ, W, W', Φ)` and `Ψ(κ, W̃, W̃', Φ̂)`, with a sign, for the
  `(σ, ψ)` pairs `(θ, κ)`. The adjacent pair `(n, n - 1)` is similar.
- (2.5) and Theorem 2.1(iii), p. 6, supply the integrals for ranks `n > m + 1`. There the
  Library's unequal dual integral is Jacquet's `Ψ_j(1 - s, ρ(w_(n,m)) W̃, W̃')` for
  `j = n - m - 1`, with the larger rectangular kernel (2.5), and its partner is
  `Ψ_0(s, W, W')`. Jacquet does not display a pair identity for these ranks. The unequal
  premise applies the method of §8.1 to this pair of integrals.

This module uses one direction of the equivalence (module `ArchimedeanRealPairIdentity`) for
the uniform coefficient spaces used by the Library's real-place reduction.

**Signs.** The signs are those of the Library's continuation statements, and they agree with
Theorem 2.1(iii), p. 6. Here `det_ds(-1)` is the product of the block determinant values at
`-1`. It plays the role of `ω_π(-1)`, since Jacquet notes `det σ_u = ω_π` (p. 7). In unequal
rank `det_ds(-1)^(t+1) · det_es(-1)` corresponds to `ω_π(-1)^m ω_π'(-1)` with `m = t + 1`. In
equal rank `det_ds(-1)^r` corresponds to `ω_π(-1)^(n-1)` with `n = r + 1`. This is also the sign `∏_i μ_i(-1)^(n-1)` produced by the computation of §8.2
(p. 56). The lower display on p. 53, the equal-rank pair identity, has the factor
`∏_i μ_i(-1)^(-n-1) ∏_j ν_j(-1)` instead. Its extra factor `∏_j ν_j(-1)` can equal `-1`, and
the equal-rank premise does not use that display's sign.

The other differences from Jacquet's formulation are described in
`ArchimedeanRealPairIdentity.md`:
- the class of pairs `(h, k)` is different;
- the factor `sign` sits in the Mellin transform of `h`;
- the Mellin normalization is Mathlib's.

**Not proved here.** The two pair-identity premises, i.e. Jacquet §§8–11 for these
coefficient spaces, and `RealPlaceContragredientPairLStatement`.
