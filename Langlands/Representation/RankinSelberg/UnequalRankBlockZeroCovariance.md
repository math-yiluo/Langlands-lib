# Covariance of the block-zero continuation families

Authors: Worker 822 (Lean) and Worker 233 (Markdown). Part of the proof task
`4564f536-d9dc-4d9a-aeb5-4ee980417bd3` for the published statement
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`; its
consumer is `UnequalRankBlockZeroContinuedFormsProof`.

This module proves the two covariance laws of JPSS (2.11.2) and (2.11.4) for
two integrals: the actual original integral of block `(0, k)`, and the
complementary inverse-transpose integral of block `(k, 0)` of the dual model
vectors. It proves them first as identities of integrals, valid at every
complex `s`, and then transfers them to the continuation families of
`UnequalRankBlockZeroContinuationFamily`, where each law multiplies the
family by a constant times a monomial `X^m`. The two operations are
simultaneous right translation by `ι(g)` and `g`, and right translation of
the first vector by an element `u` of `U_(n+2,r+1)`.

The setting is a field `F` with a topology and a measurable structure, an
absolute value `abv`, an additive character `ψ`, a measure `μ` on
`LeftUnipotentQuotient n F = N \ GL_(n+1)(F)` and a measure `ρ` on the
rectangular variables `Matrix (Fin j) (Fin (n + 1)) F`. The representations
`π`, `σ` with Whittaker functionals `ℓ`, `ℓ'` live in independent universes.
The integral and family sections assume `[IsTopologicalRing F]`; the two
original unipotent laws omit it, and the first two sections need only a
field. Apart from the `SFinite` and `BorelSpace` instances, every hypothesis
on `μ` and `ρ` is an explicit argument. The Proof module supplies the
p-adic instances.

Nothing published is redefined. The module uses `unequalRankIntegralAt`,
`determinantWeight`, `inverseTranspose`, `appendIdentity`, `blockWeylAt`,
`standardCharacter`, `IsUnequalRankCovarianceUnipotent`, `firstDualFunction`,
`secondDualFunction`, `translateWhittaker`, `translatedFirstDualModelEquiv`,
`secondDualModelMap`, `inverseTransposePullback`, `firstDualFunctional`,
`secondDualFunctional` and `modelRepresentation` as published.

Notation. `ι(g)` is the embedding of the covariance predicate
`IsUnequalRankBilinearCovariant`, that is
`GeneralLinear.reindex (finCongr _) (appendIdentity n (r - n) g)`, the matrix
`diag(g, I_(r-n))` in `GL_(r+1)`. `|det g|^t` is `determinantWeight abv g t`,
and `g⁻ᵀ` is `inverseTranspose (n + 1) F g`. `w_B` is
`blockWeylAt n r hnr = diag(I_(n+1), w_(r-n))`, with `w` the long Weyl element.
`M(g, x)` is `unequalRankMatrix j k g x`. `ψ_r(u)` is
`standardCharacter ψ r u`, the value of `ψ` at the sum of the first
superdiagonal of `u`. By the published definitions,
`firstDualFunction ψ r W` and `secondDualFunction ψ n W'` are
`h ↦ W(w · h⁻ᵀ)` and `h ↦ W'(w · h⁻ᵀ)`, and
`translateWhittaker _ r W a` is `h ↦ W(h a)`.

## Auxiliary identities

- `determinantWeight_inverseTranspose`: `|det g⁻ᵀ|^s = |det g|^(-s)` for every
  `g` in `GL_d(F)` and every complex `s`. Proof: the published
  `abv_det_inverseTranspose` gives `|det g⁻ᵀ| = |det g|⁻¹`. Then
  `Complex.inv_cpow` (the base is a nonnegative real, so its argument is not
  `π`) and `Complex.cpow_neg`.
- `inverseTranspose_mul_embedding`: for `h` in `GL_(r+1)(F)` and `g` in
  `GL_(n+1)(F)`,

  `(h w_B)⁻ᵀ · ι(g) = (h · ι(g⁻ᵀ) · w_B)⁻ᵀ`.

  Proof: `ι` commutes with the inverse transpose (`inverseTranspose_embedding`)
  and `w_B` commutes with `ι(g)` (`blockWeylAt_mul_embedding`), both from
  `UnequalRankBlockCoordinates`. The inverse transpose is multiplicative and
  involutive.

## Covariance of the integrals

- `unequalRankIntegralAt_translate`: the right-translation law
  `unequalRankIntegral_translate` of `UnequalRankBlockZeroIntegralLaws`,
  restated for the transported integral `unequalRankIntegralAt j k hr` with
  `hr : r = n + (j + k + 1)` and the embedding `ι` of the covariance
  predicate. Assume that the quotient's measurable structure is Borel, that
  `μ` is preserved by every right translation, that
  `∫ G (x g) ∂ρ = |det g|^(-j) · ∫ G x ∂ρ` for every `G`, and that
  `W₂(h) = W₁(h ι(g))` and `W'₂(h) = W'₁(h g)` for all `h`. Then for every
  complex `s`

  `I(W₂, W'₂)(s) = |det g|^((j+k+1)/2 - s - j) · I(W₁, W'₁)(s)`.

  Proof: `subst hr`, then `unequalRankIntegral_translate`.
  `reindex_appendIdentity_eq` identifies `ι(g)` with
  `appendIdentity n (j + k + 1) g`.
- `originalIntegralAt_unipotent` (JPSS (2.11.4), original integral): block
  `(0, k)`, any measure `ρ` on the empty matrices `Fin 0 × Fin (n + 1)`, and
  `u` in `U_(n+2,r+1)` (`IsUnequalRankCovarianceUnipotent n u`). If
  `W₂(h) = W₁(h u)` for all `h`, then for every inverse Whittaker function
  `W'` and every complex `s`

  `I(W₂, W')(s) = ψ_r(u) · I(W₁, W')(s)`.

  Proof: `unequalRankIntegral_of_inner_change` with `φ` the identity, so the
  measure hypothesis holds by `rfl`. With no rectangular rows,
  `M(g, x) = diag(g, I)` (the published `unequalRankMatrix_zero_rows`).
  `originalUnipotent_identity` gives an upper unipotent `u'` with the same
  first-superdiagonal sum as `u` and `diag(g, I) u = u' diag(g, I)`. So
  `W₂(diag(g, I)) = W₁(u' diag(g, I)) = ψ_r(u') W₁(diag(g, I))` by the
  Whittaker property of `W₁`, and `ψ_r(u') = ψ_r(u)`. The identity holds
  pointwise, so no change of variables is needed.
- `dualIntegralAt_unipotent` (JPSS (2.11.4), complementary integral): block
  `(k, 0)` with `hr : r = n + (k + 0 + 1)` and character `ψ.scale (-1)`.
  Assume `ρ` is invariant under every affine map `x ↦ A x + c` with
  `det A = 1`:

  `∫ G (A x + c) ∂ρ = ∫ G x ∂ρ` for every `k × k` matrix `A` with
  `det A = 1`, every `c` and every `G`.

  Let `u` be in `U_(n+2,r+1)` and `W₂(h) = W₁(h u)` for all `h`. Write
  `W₁^∨ = translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W₁) w_B`,
  and similarly `W₂^∨`. Then for every `W'` in
  `InverseWhittakerFunctions (ψ.scale (-1)) n` and every complex `s`

  `I(W₂^∨, W')(s) = ψ_r(u) · I(W₁^∨, W')(s)`.

  Proof: `dualUnipotent_identity` gives `n₀` in `U_(r+1)`, a `k × k` matrix
  `A` with `det A = 1` and a matrix `c` such that the first-superdiagonal sum
  of `n₀` is minus that of `u` and

  `M(g, x) · w_B · u⁻ᵀ = n₀ · M(g, A x + c) · w_B` for all `g`, `x`.

  Taking inverse transposes gives
  `(M(g, x) w_B)⁻ᵀ · u = (n₀ M(g, A x + c) w_B)⁻ᵀ`. Hence
  `W₂^∨(M(g, x)) = W₁(w · (M(g, x) w_B)⁻ᵀ · u) =
  firstDualFunction ψ r W₁ (n₀ · M(g, A x + c) · w_B)`. The first dual function
  of `W₁` is a Whittaker function for `ψ.scale (-1)`, so `n₀` contributes the
  factor `ψ(-1 · (-Σu)) = ψ(Σu) = ψ_r(u)`. Then
  `unequalRankIntegral_of_inner_change` with `φ x = A x + c` and the affine
  invariance of `ρ` at this `A` and `c`.
- `dualIntegralAt_translate` (JPSS (2.11.2), complementary integral): block
  `(k, 0)` as above. Assume that the quotient's measurable structure is
  Borel, that `μ` is preserved by every right translation, that

  `∫ G (x g⁻ᵀ) ∂ρ = |det g⁻ᵀ|^(-k) · ∫ G x ∂ρ` for every `G`,

  and that `W₂(h) = W₁(h ι(g))` and `W'₂(h) = W'₁(h g)` for all `h`. With
  `W^∨` as above and `W'^∨ = secondDualFunction ψ n W'`, for every complex `s`

  `I(W₂^∨, W'₂^∨)(s) = |det g⁻ᵀ|^((k+0+1)/2 - s - k) · I(W₁^∨, W'₁^∨)(s)`.

  Proof: `unequalRankIntegralAt_translate` at `g⁻ᵀ`, for the character
  `ψ.scale (-1)`. Its hypotheses on the functions hold since
  `W₂^∨(h) = W₁(w (h w_B)⁻ᵀ ι(g)) = W₁(w (h ι(g⁻ᵀ) w_B)⁻ᵀ) = W₁^∨(h ι(g⁻ᵀ))`
  by `inverseTranspose_mul_embedding`, and
  `W'₂^∨(h) = W'₁(w h⁻ᵀ g) = W'₁(w (h g⁻ᵀ)⁻ᵀ) = W'₁^∨(h g⁻ᵀ)`. The lemma
  states the factor in terms of `g⁻ᵀ`. By
  `determinantWeight_inverseTranspose` it equals `|det g|^(s + (k-1)/2)`,
  which at `1 - s` is `|det g|^((k+1)/2 - s)`, the exponent `(r-n)/2 - s` of
  (2.11.2), because `r - n = k + 1`. The Proof module makes this conversion.

## Covariance of the continuation families

Each law below is an instance of `blockContinuationFamily_of_integral`: an
identity `I₂(t) = c · spectralPoint q t ^ m · I₁(t)` for every complex `t`
gives `family₂ = C c · X^m · family₁` as rational functions. All assume
`hq : 1 < q` and s-finite `μ` and `ρ`. `blockContinuationFamily hq hA` is the
family of an analytic premise
`hA : UnequalRankAnalyticAt j k hr q ψ abv μ ρ π σ ℓ ℓ'`.

- `blockContinuationFamily_translate` (any block `(j, k)`): assume the
  hypotheses on `μ` and `ρ` of `unequalRankIntegralAt_translate`, and
  `|det g| = q^m` with `m : ℤ`. If the model vectors satisfy
  `f₂(h) = f₁(h ι(g))` and `f'₂(h) = f'₁(h g)`, then

  `family(f₂, f'₂) = C(|det g|^((j+k+1)/2 - j)) · X^m · family(f₁, f'₁)`.

  Proof: `unequalRankIntegralAt_translate`. The exponent splits as
  `((j+k+1)/2 - j) + (-t)` (`determinantWeight_exponent_add` of
  `UnequalRankBlockZeroIntegralLaws`), and the
  published `determinantWeight_neg_eq_spectralPoint_zpow` gives
  `|det g|^(-t) = spectralPoint q t ^ m`.
- `originalContinuationFamily_unipotent`: block `(0, k)`, `u` in
  `U_(n+2,r+1)`. For model vectors `f`, `f'`,

  `family(π(u) f, f') = C(ψ_r(u)) · X^0 · family(f, f')`,

  where `π(u) f` is `modelRepresentation π ℓ u f`, the right translate of `f`
  by `u`. Proof: `originalIntegralAt_unipotent`.
- `dualFirstModelMap ψ π ℓ hnr` (abbreviation): the linear map
  `(translatedFirstDualModelEquiv ψ π ℓ w_B).toLinearMap` from the model of
  `(π, ℓ)` to the model of
  `(inverseTransposePullback π, firstDualFunctional ψ π ℓ)`, `f ↦ R(w_B) f̂`.
  Its value at `f` is the function `f^∨` above.
- `dualContinuationFamily_unipotent`: block `(k, 0)`, with the analytic premise
  `hAd` for `ψ.scale (-1)`, `inverseTransposePullback π`,
  `inverseTransposePullback σ`, `firstDualFunctional ψ π ℓ` and
  `secondDualFunctional ψ σ ℓ'`. Assume the affine invariance of `ρ` from
  `dualIntegralAt_unipotent`. For `u` in `U_(n+2,r+1)` and model vectors `f`,
  `f'`,

  `family_d(D₁(π(u) f), D₂ f') = C(ψ_r(u)) · X^0 · family_d(D₁ f, D₂ f')`,

  with `family_d = blockContinuationFamily hq hAd`,
  `D₁ = dualFirstModelMap ψ π ℓ hnr` and `D₂ = secondDualModelMap ψ σ ℓ'`.
  Proof: `dualIntegralAt_unipotent`.
- `dualContinuationFamily_translate`: block `(k, 0)` and `hAd` as above. Assume
  the hypotheses on `μ` and `ρ` of `dualIntegralAt_translate` and
  `|det g⁻ᵀ| = q^m`. Then

  `family_d(D₁(π(ι(g)) f), D₂(σ(g) f')) =
  C(|det g⁻ᵀ|^((k+0+1)/2 - k)) · X^m · family_d(D₁ f, D₂ f')`.

  Proof: `dualIntegralAt_translate`, then the same exponent splitting as in
  `blockContinuationFamily_translate`.

The Proof module evaluates these identities with `eval_C_mul_X_zpow_mul` at
`spectralPoint q s` (original family) and at `spectralPoint q (1 - s)`
(complementary family). This gives the two clauses of
`IsUnequalRankBilinearCovariant` for `B` and `Bdual`. There the hypotheses on
`ρ` come from `rectangularMeasure_zero_rows_translate` (`j = 0`) and from the
published `padicRectangularHaarScaling` (`j = k`).

## Provenance

JPSS = H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. **105** (1983), §2.11, printed pp.398–399
(one-based PDF pages 33–34 of the registered scan `jpss-1983-rankin-selberg`).
With printed ranks `r, t` equal to Lean `r + 1, n + 1`, (2.11.2) corresponds
to `blockContinuationFamily_translate` (for `j = 0`) and
`dualContinuationFamily_translate`. Formula (2.11.4), for `u ∈ U_(t+1,r)`
(Lean `IsUnequalRankCovarianceUnipotent n u`), corresponds to
`originalContinuationFamily_unipotent` and
`dualContinuationFamily_unipotent`. The Proof module evaluates these
identities to obtain the statements for `B` and `Bdual`. JPSS states both
for the continued integrals "except for finitely many `q^{-s}`". For the
complementary integral `Ψ(1-s, ρ(w_{r,t}) W̃, W̃'; r-t-1)` (JPSS's `ρ` is
right translation, not the measure of this module) it says only
"similarly". JPSS gives no proof (compare the change-of-variables
computations in §2.10, pp.395–397). The proofs here are internal to this
proof task. They consist of the matrix identities of
`UnequalRankBlockCoordinates`, the inner change of variables `x ↦ A x + c`
with `det A = 1` on the complementary side, and transfer to the
continuations through uniqueness of rational continuations.
The sign of the character on the complementary side cancels: the dual
integral has character `ψ.scale (-1)` and `n₀` has superdiagonal sum `-Σu`,
so both forms get the same factor `ψ_r(u)`. The current registration, the
central library, and the project and Library note locations were checked for
errata. No registered erratum to JPSS 1983 was found. The registered Jacquet
2012 correction concerns the 1981 conductor paper only.
