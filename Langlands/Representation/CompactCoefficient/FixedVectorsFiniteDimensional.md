# Finite-dimensional fixed vectors of irreducible compact-coefficient representations

This module proves the irreducible case of Bernstein--Zelevinsky (1976), Corollary 2.41
(printed page 26): an irreducible finite representation is admissible. It does so for an
arbitrary topological group, following the first step (`dim E_ξ < ∞`) of the proof of
Lemma-Definition 2.40 a) ⇒ b); the compactness assertion 2.40 b) itself is not proved here. Throughout,
`G` is a topological group with Borel measurable structure and a left Haar measure `μ`
(`μ.IsHaarMeasure`). `N` is an open subgroup of `G` with compact underlying set (`hN`).
`ρ` is a smooth complex representation (`hρ : IsSmooth ρ`). Only left invariance of `μ`
is used; the module needs neither unimodularity nor right invariance.

Provenance (derived). In the source a representation is *finite* when all matrix
elements `g ↦ ⟨ξ̃, π(g⁻¹) ξ⟩` against smooth dual vectors `ξ̃` have compact support;
this is the Library's `HasCompactSmoothDualCoefficients` (it is not finite
dimension). The source proof of a) ⇒ b) shows that the vectors `π(e_N) π(g⁻¹) ξ`
span a finite-dimensional space by building a smooth functional with value `i` on the
`i`-th of infinitely many independent such vectors. The Lean proof follows the same
idea for an irreducible representation, with the functional built from a basis inside
the averaged orbit: its coefficient takes the value `1` on every basis vector, so the
basis lies in the image of a compact set under a locally constant map. The
definitions `inverseCoefficient`, `dualAverage` and `fixedExtension` are internal
auxiliary constructions of this proof (averaging over `N` replaces the source's use
of `π(ε_N)` on the dual side).

## Inverse coefficients

`apply_eq_of_mem_fixedVectors` unfolds membership in `fixedVectors ρ K`: a `K`-fixed
vector satisfies `ρ k v = v` for `k ∈ K`.

For a smooth dual vector `ℓ` (`IsSmoothVector ρ.dual ℓ`) and compact smooth-dual
coefficients (`HasCompactSmoothDualCoefficients ρ`), the following holds.

- `inverseCoefficient ρ hρ hc ℓ hℓ` is the linear map `V → SchwartzBruhat G`
  given by `v ↦ (g ↦ ℓ (ρ g⁻¹ v))`.
  - The function is locally constant because orbit maps of smooth vectors are
    locally constant.
  - It has compact support because a matrix coefficient composed with the
    inversion homeomorphism still has compact support.
- `inverseCoefficient_apply_rho`: replacing `v` by `ρ h v` left-translates the
  function (`TestFunction.leftTranslate h`).
- `inverseCoefficient_mem_biInvariant`: if `ℓ` is `K`-invariant and `v` is
  `K`-fixed, the function is bi-`K`-invariant.

## Averaging functionals over `N`

`dualAverage μ ρ hρ N hN ℓ y = μ(N)⁻¹ ∫_N ℓ (ρ k⁻¹ y) dμ(k)`.

- The integrand is continuous on the compact set `N`, hence integrable.
- `dualAverage_apply_of_fixed`: on `N`-fixed vectors the average is `ℓ`.
  This uses `setIntegral_const` and `compactOpen_complex_mass_ne_zero`.
- `dualAverage_apply_rho`: the average is `N`-invariant. Write the set integral
  as the integral of an indicator and use left invariance
  (`integral_mul_left_eq_self`).
- `dualAverage_isSmoothVector`: the average is a smooth dual vector.
- `apply_heckeAction_normalizedIndicator`: an `N`-invariant functional `Λ`
  satisfies `Λ (ρ(e_N) y) = Λ y`, where `e_N` is the normalized indicator of
  `N`. The proof uses `integratedAction_dual`.

## Finite-dimensional fixed vectors (BZ Corollary 2.41, irreducible case)

`fixedExtension μ ρ hρ N hN ℓ` extends a functional `ℓ` on the `N`-fixed
vectors to `dualAverage (ℓ ∘ P_N)`, where `P_N = fixedProjection`.
`fixedExtension_apply` shows that the extension equals `ℓ ∘ P_N` everywhere, and
`fixedExtension_isSmoothVector` that it is a smooth dual vector.

`finiteDimensional_fixedVectors` takes `ρ` irreducible with compact smooth-dual
coefficients and concludes that the `N`-fixed vectors are finite-dimensional.

1. Choose a nonzero fixed vector `ξ` (the zero case is trivial).
2. The vectors `u g = P_N (ρ g ξ)` span the fixed space, because the orbit of
   `ξ` spans `V` (`span_range_orbit_eq_top`) and `P_N` is onto the fixed space.
3. Choose a basis `b` of the fixed space inside the range of `u`
   (`exists_linearIndependent`). Let `Λ` be the extension of `b.sumCoords`.
4. The coefficient `g ↦ Λ (ρ g ξ)` equals `b.sumCoords (u g)` and has compact
   support.
5. `u` is locally constant, so the image under `u` of this compact support is
   finite (discrete topology, `IsCompact.finite_of_discrete`).
6. Each basis vector `u g` has `sumCoords = 1`, so `g` lies in the support.
   Hence the basis is finite.
