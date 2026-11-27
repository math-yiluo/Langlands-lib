# Conjugation counts on a discrete left quotient

Module `Langlands.Global.LeftCosetConjugationCount`, namespace
`Langlands.Global.LeftCosetSpace`. It bounds integrals of conjugation counts over a discrete
left quotient `Γ \ H` by unfolding. The module
`Langlands.Global.AdelicRationalQuotientSummableLogHeightProof` applies it to
`G(F) \ G(𝔸)`.

## Setting

`H` is a group and `Γ` a subgroup. For the measure statements `H` is a second-countable
topological group with its Borel σ-algebra, `Γ` is discrete (`IsDiscrete (Γ : Set H)`), and `ν`
is a left-invariant measure on `H` (`ν.IsMulLeftInvariant`). The measure on `Γ \ H` is the
Library's `discreteQuotientMeasure Γ hΓ ν`, the pushforward of `ν` restricted to the Borel
fundamental domain `fundamentalDomain Γ hΓ`. A coset `y` has the chosen representative `y.out`.

## Definitions

- `conjugationCount Γ C t` is `#{q ∈ Γ : t⁻¹ q t ∈ C}` as an element of `ℝ≥0∞`. It is the
  coercion of `Set.encard {q : H | q ∈ Γ ∧ t⁻¹ * q * t ∈ C}`. This is the count of
  `RationalQuotientSummableLogHeightStatement` (module
  `Langlands.Global.AdelicTemperedComponentInputs`).
- `translateCount Γ A t` is `#{γ ∈ Γ : γ t ∈ A}`, written as the sum over `γ ∈ Γ` of the
  indicator of `A` at `γ t`.

## Statements

- `translateCount_mul`: for `γ₀ ∈ Γ`, `translateCount Γ A (γ₀ t) = translateCount Γ A t`.
- `conjugationCount_le_translateCount`: let `C, D ⊆ H` and `t = γ₀ x d` with `γ₀ ∈ Γ` and
  `d ∈ D`. Then `conjugationCount Γ C t ≤ translateCount Γ A t`, where
  `A = {u : x⁻¹ u ∈ D C}` is the translate `x (D C)`.
- `measurable_translateCount`: for countable `Γ` and measurable `A`, `translateCount Γ A` is
  measurable.
- `lintegral_translateCount_out` (unfolding): for measurable `A`,
  `∫⁻ translateCount Γ A (y.out) d(discreteQuotientMeasure Γ hΓ ν)(y) = ν(A)` (lower Lebesgue
  integral).
- `lintegral_conjugationCount_mul_le`: let `y : ι → H` be a family indexed by a countable type.
  Let `C, D ⊆ H` with `D C` measurable, let `w : Γ \ H → ℝ≥0∞` and `Φ : ι → ℝ≥0∞`. Assume that
  every coset `z` has an index `i`, some `γ ∈ Γ` and some `d ∈ D` with `z.out = γ y_i d` and
  `w z ≤ Φ i`. Then

  `∫⁻ conjugationCount Γ C (z.out) · w z d(discreteQuotientMeasure Γ hΓ ν)(z) ≤ (∑ᵢ Φ i) · ν(D C)`,

  with the lower Lebesgue integral `∫⁻`. No measurability of `w` is assumed.

## Proofs

- `translateCount_mul`: reindex the sum over `Γ` by right multiplication with `γ₀`
  (`Equiv.mulRight`, `Equiv.tsum_eq`).
- `conjugationCount_le_translateCount`: if `q ∈ Γ` and `t⁻¹ q t = c ∈ C`, then
  `x⁻¹ (γ₀⁻¹ q) t = d c ∈ D C` (a group computation from `t = γ₀ x d`). The map
  `q ↦ γ₀⁻¹ q` is injective from the counted set into `Γ`, and each image term of the
  translate count equals `1`. The encard is the sum of `1` over the set (`ENNReal.tsum_set_one`),
  and `ENNReal.tsum_comp_le_tsum_of_injective` compares the two sums.
- `measurable_translateCount`: a countable sum of indicators of the measurable sets
  `(γ ·)⁻¹' A` (`Measurable.tsum`).
- `lintegral_translateCount_out`: the integrand is measurable and left `Γ`-invariant, so
  `measurable_comp_out`, `apply_out_mk` and `lintegral_map` turn the left side into
  `∫⁻_s translateCount Γ A dν` over the fundamental domain `s`. Exchanging sum and integral
  (`lintegral_tsum`) gives `∑_γ ∫⁻_s 1_A(γ x) dν(x)`, which is `∫⁻ 1_A dν = ν(A)` by
  `IsFundamentalDomain.lintegral_eq_tsum''` (applied to `isFundamentalDomain Γ hΓ ν`).
- `lintegral_conjugationCount_mul_le`: put `A_i = {u : y_i⁻¹ u ∈ D C}`. By the hypothesis and the
  count comparison, for every coset `z` there is `i` with
  `conjugationCount Γ C (z.out) · w z ≤ Φ i · translateCount Γ A_i (z.out)`, which is at most the
  sum of these terms over all `i`. Integrate, exchange the sum and the integral (each term is
  measurable by `measurable_comp_out`), and use `lintegral_translateCount_out` and the left
  invariance `ν(A_i) = ν(D C)` (`measure_preimage_mul`). The result is `∑ᵢ Φ i · ν(D C)`.

## Provenance

The count and its comparison with a translate count are derived from the counting form of
Bernstein's standard measure. The Markdown of `RationalQuotientSummableLogHeightStatement`
explains this form. J. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5
(1988), 663–710 (`bernstein-1988-support-plancherel`), §3.3 (pp. 683–685): the standard measure
on `X` has density `μ_X(Bx)⁻¹` for a ball `B`. Here the translate count at `t` of a translate
`x B'` is the periodized indicator `P_{B'}(x, ·)`, and unfolding gives its integral `ν(B')`.
The last statement is analogous to the criterion of Bernstein's §3.2 (pp. 682–683) for a
sparse net. A net has a covering ball `B` (`B · 𝒩 = X`). It is sparse if, for every ball `Ω` in
the acting group, the number of points of `𝒩 ∩ Ω x` is bounded by a constant `k(𝒩, Ω)`
independent of `x ∈ X` (p. 682). For a sparse net, summability of `w` is equivalent to
`∑_{n ∈ 𝒩} w(n)⁻¹ < ∞`, a sum of reciprocal weights at the points of the net. Here the images
of the translates `y_i D` cover `Γ \ H`, and `Φ i` is an upper bound for `w` on the cosets
assigned to `i`. It need not be a value of `w` at a point attached to `y_i`, and the family need
not be sparse. The proofs are the elementary measure theory written above. They do not use
Bernstein's weight-measure comparisons.
