# The unfolding identity for abstract locally compact groups

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingAbstract`, namespace
`Langlands.Global.LeftCosetSpace`.

## Helpers

- `setIntegral_fundamentalDomain_mul_right`: let `Δ` be a discrete subgroup of a locally compact
  second countable group `X` such that one compact set meets every orbit of `Δ`, so that the
  normalized Haar measure is right invariant. For a left `Δ`-invariant function `g`, the integral
  of `x ↦ g(x x₀)` over the chosen fundamental domain equals that of `g`, for every `x₀`.
- `measurable_setIntegral_subgroup_mul`: for a subgroup `X`, an s-finite measure `μ` on `X`, a set
  `s ⊆ X` and a measurable `h : 𝒢 → ℂ`, the function `x ↦ ∫_{u ∈ s} h(u x) dμ` is measurable.
- `setIntegral_latticeOf_mul_left`: for a closed subgroup `U'` such that one compact set meets
  every orbit of `U' ∩ R`, the normalized average over the chosen fundamental domain of `U' ∩ R`
  in `U'` of `u ↦ h(u x)`, for `h` left invariant under `U' ∩ R`, is unchanged when `x` is
  replaced by `u x` with `u ∈ U'`.

## Main result

`integral_unfolding_eq`: let `R` be a discrete subgroup of the second countable locally compact
Hausdorff group `𝒢`, `w ∈ R`, and `V ≤ V'`, `U ≤ U'`, `A ≤ U'`, `B ≤ V'` closed subgroups with
`w A w⁻¹ ⊆ V` and `w⁻¹ B w ⊆ U`, such that

- `U' = U ⋊ A`: `U` is normalized by `U'`, `A ∩ U = 1`, `U' = U A`, and the `A`-component of every
  element of `U' ∩ R` lies in `R`;
- `V' = V ⋊ B`: `V` is normalized by `V'`, `B ∩ V = 1`, `V' = V B`, and the `B`-component of every
  element of `V' ∩ R` lies in `R`;
- for each of `V`, `V'`, `U`, `U'`, `V ∩ w U w⁻¹` and `V ∩ w U' w⁻¹`, one compact set meets every
  orbit of its intersection with `R`.

Normalize all Haar measures by these intersections with `R` (`normalizedHaar`) and put
`C(x) = ∫_{fd(U' ∩ R)} h(u x) du`. If `h : 𝒢 → ℂ` is measurable and left invariant under `U` and
under `U' ∩ R`, and `v ↦ h(w⁻¹ v y)` has finite absolute integral over the chosen fundamental
domain of `V ∩ R ∩ w U' w⁻¹` in `V`, then `x ↦ C(w⁻¹ x y)` is integrable over the chosen
fundamental domain of `V' ∩ R ∩ w U' w⁻¹` in `V'`, and

`∫_{fd(V' ∩ R ∩ w U' w⁻¹)} C(w⁻¹ x y) dx = ∫_{fd(V ∩ R ∩ w U' w⁻¹)} h(w⁻¹ v y) dv`.

## Proof

A compatible quotient measure `ν` on `(V ∩ w U' w⁻¹) \ V` exists (`compatibleMeasureExists`).
The right side, the integral of `h` over the fundamental domain in `V`, is
`∫_q ∫_n h(w⁻¹ n q̄ y) dn dν(q)` by `integral_transversal_eq`, which also gives integrability of
the inner integral in `q`; by `setIntegral_inner_eq` the inner integral is `C(w⁻¹ q̄ y)`. The
function `C` is left invariant under `U'` (a direct application of
`setIntegral_fundamentalDomain_mul_right` to `U' ∩ R`), so `Φ(x) = C(w⁻¹ x y)` on `V'` is left
invariant under `V' ∩ w U' w⁻¹`. For the left side, the integral of `Φ` over the fundamental
domain in `V'`, `integral_rightTransversal_eq` gives integrability and identifies it with the same
`∫_q C(w⁻¹ q̄ y) dν(q)`.

## Provenance

The chain of equalities of the proof of Bernstein–Lapid Lemma 6.10, journal pp. 208–209, from
`∫_{(U_Q ∩ w U_{P_w} w⁻¹)(F) \ U_Q(A)} φ_λ(w⁻¹ u γ g) du` to the intertwining integral of the
constant term, for abstract groups.
