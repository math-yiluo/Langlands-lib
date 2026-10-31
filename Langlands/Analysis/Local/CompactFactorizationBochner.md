# Pushforward and Bochner forms of the factorization integral

Module `Langlands.Analysis.Local.CompactFactorizationBochner`.

Author: Worker 1112. The proof of `lintegral_restrict_lintegral_mul_of_support`
adapts Worker 235's published proof of `lintegral_restrict_lintegral_mul`
(`Langlands.Analysis.Local.CompactFactorizationIntegral`).

## Setting

As in `Langlands.Analysis.Local.CompactFactorizationIntegral`: `G` is a group
with a left-invariant s-finite measure `μ`, `K ≤ G` is a measurable subgroup,
`ρ` is an s-finite measure on a parameter space `X`, and `ι : X → G` is
measurable. The hypotheses are:

- `hfac`: every `y : G` has the form `ι x₀ * k₀` with `k₀ ∈ K`;
- `hσ`: for every `x₀`, left translation by `(ι x₀)⁻¹` is represented on `X` by
  a `ρ`-preserving map `σ`, i.e. `ι (σ x) = (ι x₀)⁻¹ * ι x`.

## Definition

`factorizationMap ι : G × X → G` is the map `(k, x) ↦ ι x * k`
(`factorizationMap_apply`, `factorizationMap_eq`).

## Results

- `map_restrict_prod_mul`: the pushforward of `μ|_K × ρ` under
  `factorizationMap ι` equals `ρ (ι ⁻¹' K) • μ`.
  Proof: evaluate both measures on a measurable set `A`. The left side is the
  product-measure integral of the indicator of the preimage; Tonelli
  (`lintegral_prod`) turns it into the iterated integral
  `∫⁻ k in K, ∫⁻ x, 1_A (ι x * k) dρ dμ`, which
  `lintegral_restrict_lintegral_mul` (applied to `1_A`) evaluates as
  `ρ (ι ⁻¹' K) * μ A`.
- `integrable_comp_mul_iff`: if `0 < ρ (ι ⁻¹' K) < ∞` and `F` is
  a.e.-strongly measurable for `μ`, then `(k, x) ↦ F (ι x * k)` is integrable
  for `μ|_K × ρ` exactly when `F` is `μ`-integrable. Proof: integrability along
  the pushforward (`integrable_map_measure`), the identity above, and
  invariance of integrability under a finite nonzero scalar multiple of the
  measure (`integrable_smul_measure`).
- `integral_restrict_integral_mul`: for `F` integrable on `G` with values in a
  real normed space,
  `∫ k in K, ∫ x, F (ι x * k) dρ dμ = (ρ (ι ⁻¹' K)).toReal • ∫ y, F y dμ`.
  Proof: `integral_smul_measure`, the pushforward identity, `integral_map`, and
  Fubini (`integral_prod`) using the integrability transfer above.

## Scope

These are abstract measure-theoretic statements; they are the Bochner-integral
counterparts of the nonnegative factorization integral and are used to factor
Haar integrals on `GL_N` over a parabolic times a compact open subgroup. No
quotient measures and no compactness of `K` are needed here; the finiteness and
positivity of `ρ (ι ⁻¹' K)` are hypotheses.

## Functions supported in `ι(X) K`

The same identities hold without `G = ι(X) K` for functions supported in a
measurable set `S` with `S = ι(X) K` (hypotheses `hSfac` and `hSK`).

- `lintegral_restrict_lintegral_mul_of_support`: the nonnegative factorization
  identity for a measurable `F` that vanishes off `ι(X) K`. The proof repeats
  the Tonelli argument of `lintegral_restrict_lintegral_mul`; in the step that
  evaluates the parameter integral at a point `y`, the case `F y = 0` is
  trivial, and otherwise the support hypothesis supplies the factorization
  `y = ι x₀ * k₀` used there.
- `map_restrict_prod_mul_of_subset`: the pushforward of `μ|_K × ρ` under
  `factorizationMap ι` is `ρ (ι ⁻¹' K) • μ|_S`. Proof: apply the previous
  identity to the indicator of `A ∩ S`, using that `ι x * k ∈ S` for `k ∈ K`.
- `integrable_comp_mul_iff_of_subset` and
  `integral_restrict_integral_mul_of_subset`: the integrability transfer and the
  Bochner identity
  `∫ k in K, ∫ x, F (ι x * k) dρ dμ = (ρ (ι ⁻¹' K)).toReal • ∫ y in S, F y dμ`,
  proved exactly as in the case `S = G`.

## Integrals of compact coefficient formulas

Let `ν` be a measure on a parameter space `κ` with a measurable map `j : κ → G`
(in applications `κ` is a compact open subgroup and `ν` its Haar probability
measure). For `H : G → ℂ` and `Γ : κ → G → ℂ`, consider the function
`g ↦ H g * ∫ k, Γ k (j k * g) dν`, i.e. a zeta integrand times a coefficient
given by a compact integral formula, and the function
`Ψ (k, y) = H ((j k)⁻¹ * y) * Γ k y` on `κ × G`.

- `integrable_integral_coefficient_of_integrable`: if `Ψ` is integrable for
  `ν × μ`, then `g ↦ H g * ∫ k, Γ k (j k * g) dν` is `μ`-integrable and its
  integral equals `∫ Ψ d(ν × μ)`. Proof: the skew map `(k, g) ↦ (k, j k * g)`
  preserves `ν × μ` (`MeasurePreserving.skew_product` with left invariance of
  `μ`), and it carries `Ψ` to `(k, g) ↦ H g * Γ k (j k * g)`; then Fubini
  (`Integrable.integral_prod_right`, `integral_prod_symm`) and pulling the
  constant `H g` out of the `k`-integral.
- `map_prod_prod_factorization`: if `j' : κ' → G` pushes a measure `ν'` forward
  to `μ|_K`, the map `(k, (k', x)) ↦ (k, ι x * j' k')` pushes `ν × (ν' × ρ)`
  forward to `ρ (ι ⁻¹' K) • (ν × μ)` (`map_prod_map`, `map_restrict_prod_mul`,
  `Measure.prod_smul_right`).
- `integrable_integral_coefficient_of_expansion`: assume
  `0 < ρ (ι ⁻¹' K) < ∞`, the factorization hypotheses, a.e.-strong
  measurability of `Ψ`, and a finite expansion
  `H ((j k)⁻¹ * (ι x * j' k')) * Γ k (ι x * j' k') = ∑ r ∈ s, ψ r k k' * Q r x`
  for all `k, k', x`, where each `(k, k') ↦ ψ r k k'` is `ν × ν'`-integrable and
  each `Q r` is `ρ`-integrable. Then `g ↦ H g * ∫ k, Γ k (j k * g) dν` is
  `μ`-integrable and
  `∫ g, H g * ∫ k, Γ k (j k * g) dν dμ =
   (ρ (ι ⁻¹' K)).toReal⁻¹ • ∑ r ∈ s, (∫ ψ r d(ν × ν')) * ∫ Q r dρ`.
  Proof: by the pushforward identity, `Ψ` composed with
  `(k, (k', x)) ↦ (k, ι x * j' k')` is the finite sum of products, which is
  integrable (`Integrable.mul_prod` after reassociating the product measure
  with `measurePreserving_prodAssoc`); integrability and the integral transfer
  back to `ν × μ` (`integrable_map_measure`, `integrable_smul_measure`,
  `integral_map`, `integral_smul_measure`), and `integral_prod_mul` splits
  each product. The previous substitution lemma finishes.
- `integrable_integral_coefficient_of_translate`: for finite `ν`, if
  `y ↦ Ψ (k, y)` is a left translate `y ↦ Ψ₀ (g₀ * y)` of one integrable `Ψ₀`
  for `k` in a measurable `S` and vanishes for `k ∉ S`, then the coefficient
  integral is integrable with integral `(ν S).toReal • ∫ Ψ₀ dμ`. Proof:
  `integrable_prod_iff` with left invariance of `μ` for each slice
  (`Integrable.comp_mul_left`, `integral_mul_left_eq_self`), Fubini, and the
  integral of an indicator of a constant.

These generic results are internal measure-theoretic tools for the
Godement–Jacquet two-block analytic induction (Godement–Jacquet 1972, Theorem
3.4, printed 38–45), where the coefficient of a normalized induced
representation is an integral over a compact open subgroup and the Haar
measure of `GL_N` is factorized over a parabolic subgroup times that compact
subgroup. They make no statement about representations.
