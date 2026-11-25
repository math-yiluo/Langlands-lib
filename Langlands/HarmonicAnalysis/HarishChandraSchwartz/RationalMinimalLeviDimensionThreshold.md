# Proposition I.4.3 on the full minimal Levi with a representation-independent threshold

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviDimensionThreshold`,
namespace `Langlands.HarishChandraSchwartz`. Helper module of the proof of
`RationalOrbitConstantTermThresholdStatement`.

## Source

Waldspurger (2003), literature id `waldspurger-2003-plancherel`: Proposition I.4.3 (printed
p. 245, PDF p. 11) is stated for all `m ∈ M̄_0^+`, the closed chamber of the minimal Levi
`M_0`, not only for points of the split torus `A_0`; I.1 (printed p. 240) defines `H_0` and
`M̄_0^+ = H_0^{-1}(ā_0^+)`. The published `StandardCasselmanUniformAsymptotics.md` records that
the Library's version treats only `Ā_0^+`; this module treats every point of the actual minimal
Levi `M_0(F) = standardLeviPoints i ν ∅`.

## Statements

- `exists_compact_dominant_depth_reduction`: from the minimal-Levi Cartan covering
  `StandardLeviCartanCovering F i ν ∅ K0` of a compact `K0` there is a compact `Q ⊆ M_0(F)` such
  that every `m ∈ M̄_0^+` (`rationalMinimalClosedChamber`) is `k₁ ϖ^y k₂` with `k₁, k₂ ∈ Q`, `y`
  dominant, and `⟨α, H_0(m)⟩ ≤ ⟨α, y⟩` for all simple `α`. The proof is the argument of the
  published `hasCompactDominantMinimalLeviReduction_of_cartanCovering` (shift by `N ν` with
  `N` bounding `⟨α, H_0(f)⟩` over the finite set `F0` of the covering), keeping the inequality
  `⟨α, H_0(f)⟩ ≤ ⟨α, N ν⟩` it proves along the way. `H_0` facts used:
  `rationalMinimalH0_mul`, `rationalMinimalH0_eq_zero_of_mem_compact`,
  `rationalMinimalH0_minimalLeviUniformizer`.
- `exists_region_dimension_threshold`: with the simultaneous basis data of
  `StandardCasselmanDimensionThreshold`, a compact `K0` with the minimal-Levi Cartan covering,
  a face `J ⊆ Δ` and a basis member `K₁ ∈ B`, there is `K₂ ∈ B` with `K₂ ≤ K₁` such that for
  every `d` there is `t > 0` with `ℓ(ρ(m) v) = b(ǰ(ℓ), j(ρ(m) v))` for every admissible `ρ`
  with `finrank (fixedVectors ρ K₂) ≤ d`, every stable pairing `b` of the I.4.1 data of `P_J`,
  all `K₁`-fixed `v`, `ℓ`, and every `m ∈ rationalConstantTermThresholdRegion J t` (the
  published region `{m ∈ M̄_0^+ ; ⟨α, H_0(m)⟩ ≥ t for α ∈ Δ ∖ J}`).

## Proof of the region theorem

Take `Q` from the reduction. The Library's
`HarmonicAnalysis.Distribution.RenardCenter.exists_openSubgroup_conj_mem` gives an open subgroup
`U` with `y U y⁻¹ ⊆ K₁` for `y` in the compact set `Q ∪ Q⁻¹`; choose `K₂ ∈ B` inside
`U ∩ K₁`. For `d`, let `T` be the threshold of
`exists_dimension_threshold_standardCasselmanPairing` for `K₂` and `d`, and `t = |T| + 1`. For
`m = k₁ ϖ^y k₂` in the region, `ρ(k₂) v` and `ρ̃(k₁⁻¹) ℓ` are `K₂`-fixed, `y` is dominant and
`⟨α, y⟩ ≥ ⟨α, H_0(m)⟩ ≥ t > T` outside `J`, so the lattice theorem gives
`ℓ(ρ(m) v) = (ρ̃(k₁⁻¹)ℓ)(ρ(ϖ^y) ρ(k₂) v) = b(ǰ(ρ̃(k₁⁻¹)ℓ), j(ρ(ϖ^y) ρ(k₂) v))`. Since
`k₁ ∈ M_0(F) ⊆ M_J(F)` (`standardLeviPoints_empty_le`), the `M_J`-invariance of stable pairings
(`IsStablePairing.map_action`) turns the right side into `b(ǰ(ℓ), j(ρ(m) v))`.

## Check

Development check: 0 errors, 0 warnings.
