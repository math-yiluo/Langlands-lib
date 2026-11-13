# Compactness modulo the centre on an open subgroup (generic lemmas for Renard VI.2.1, remarks)

Module `Langlands.Representation.CuspidalSupport.SupercuspidalRemarksGeneric`.
Namespace `Langlands.SupercuspidalRemarks`. Universe parameters `uΓ uV`.

This module contains only theorems, about an arbitrary topological group `Γ`. Write
`Z = Subgroup.center Γ`. Nothing here refers to reductive groups. The module supports
`SupercuspidalRemarksReduction`, which specializes these lemmas to `Γ = G(F)` and the
common norm kernel `H = ⁰G`.

## Provenance

These are internal, derived lemmas. They formalize the argument Renard sketches for the
second Remark 2 after the proof of the VI.2.1 Theorem (David Renard, *Représentations des
groupes réductifs p-adiques*, 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, printed p.139 / PDF p.145):
"adapt the proof of Theorem IV.1.3, using that `⁰G Z` has finite index and `⁰G ∩ Z` is
compact". The source gives no further detail. The individual steps below are written
for this formalization; they are not quoted from the book.

## Group-theoretic and topological lemmas

- `exists_finset_cosets_cover`: a compact set lies in finitely many left cosets `t N`
  of an open subgroup `N`. Proof: the cosets `g N` are open and cover, so finitely many
  suffice.
- `exists_isCompact_inter_mul_center`: if `N` is an open subgroup with `N ∩ Z` compact
  and `C` is compact, then `N ∩ C Z` lies in a compact set. Proof: cover `C` by finitely
  many cosets `t N` (`t ∈ T`). If `x = c z ∈ N` with `c = t h`, `h ∈ N`, then
  `t z = x h⁻¹ ∈ N`, because `z` commutes with `h`. So `x` lies in `C · E`, where `E` is the
  finite union over `t ∈ T` of `t⁻¹ (N ∩ t Z)`. Each `N ∩ t Z` is compact by the published
  `Langlands.isCompact_subgroup_central_coset`, so `C · E` is compact.
- `exists_finset_mul_mul_center`: if `N` is normal and `N Z` has finite index, every
  `g` can be written `g = t h z` with `t` in a fixed finite set (representatives of
  `Γ ⧸ N Z`), `h ∈ N` and `z ∈ Z`. Proof: write `g = q l` with `q` the chosen
  representative of the coset of `g` and `l ∈ N Z`. Then use `Subgroup.normal_mul` to
  split `l` as `h z`.
- `mem_inv_mul_center`: `g⁻¹ ∈ C Z` implies `g ∈ C⁻¹ Z`, because `Z` is central.

## Smooth-representation lemmas

Let `ρ : Representation ℂ Γ V`. "Smooth dual vector" means `IsSmoothVector ρ.dual ℓ`.
"Compact coefficients" means the published `HasCompactSmoothDualCoefficients`.

- `exists_openSubgroup_invariant_of_isSmoothVector_dual`: a smooth dual vector `ℓ`
  satisfies `ℓ (ρ k y) = ℓ y` for all `k` in some open subgroup.
- `exists_compact_invariant_of_isSmoothVector_dual`: given a compact open `K₀`, the
  subgroup `K₀ ∩ L` is compact open and fixes `ℓ`. It is closed in the compact `K₀`
  because open subgroups are closed.
- `exists_isCompact_uniform_support` (IV.1.3, uniform version). Assume `Γ` is locally
  compact, `ρ` is smooth with compact coefficients, and `K` is compact open. Then for
  each `w` there is one compact `S` that contains the support of `h ↦ ℓ (ρ h w)` for
  every `K`-invariant `ℓ`. Proof: take a left Haar measure and the published Hecke
  projector `e_K = Hecke.fixedProjection`. A `K`-invariant `ℓ` satisfies
  `ℓ = ℓ ∘ e_K`
  (`CompactCoefficientClass.apply_heckeAction_normalizedIndicator`). So the support
  lies in the topological support of `h ↦ e_K (ρ h w)`. That support is compact by the
  published `Renard.CompactRepresentation.hasCompactSupport_projectedOrbit` (the IV.1.3
  argument).
- `hasCompactSmoothDualCoefficients_comp_openSubgroup`: restricting to an open subgroup
  `H` keeps compact coefficients. On `H`, smooth dual vectors are the same as for `Γ`
  (`isSmoothVector_restrict_open_iff`). A coefficient on `H` is the ambient coefficient
  composed with the closed embedding `H → Γ`.
- `hasCompactSmoothDualCoefficients_comp_of_support` (compact modulo `Z` ⇒ compact on
  `H`). Assume `H` is open, `H ∩ Z` is compact and some compact open `K₀` exists.
  Suppose that for every compact open `K` and every `w` there is a compact `C` with
  `support (g ↦ ℓ (ρ g⁻¹ w)) ⊆ C Z` for all `K`-invariant `ℓ`. Then `ρ` restricted to
  `H` has compact coefficients. Proof: for a smooth dual vector `ℓ`, pick a compact
  open `K` fixing it and get `C`. Then `support (g ↦ ℓ (ρ g v)) ⊆ C⁻¹ Z`. On `H` this
  lies in `H ∩ C⁻¹ Z`, which is contained in a compact `D`
  (`exists_isCompact_inter_mul_center`). The preimage of `D` in `H` is compact because
  `H` is closed.
- `support_subset_mul_center_of_comp` (compact on `H` ⇒ compact modulo `Z`,
  uniformly in `ℓ`). Assume `Γ` is locally compact, `ρ` is smooth, `H` is open normal
  with `H Z` of finite index, and `ρ|_H` has compact coefficients. Then for every
  compact open `K` and every `w` one compact `C` works for all `K`-invariant `ℓ`.
  Proof: `H` is closed, hence locally compact, and `K' = K ∩ H` is compact open in `H`.
  Fix the finite set `T` from `exists_finset_mul_mul_center`. For each `t`, apply
  `exists_isCompact_uniform_support` to `ρ|_H`, `K'` and `ρ(t⁻¹) w`; this gives a
  compact `S_t ⊆ H`. Put `C = ⋃_{t ∈ T} t S_t⁻¹`. If `g = t h z` and
  `ℓ (ρ g⁻¹ w) ≠ 0`, set `ℓ' = ℓ ∘ ρ(z⁻¹)`. It is `K'`-invariant because `z` is
  central, and `ℓ (ρ g⁻¹ w) = ℓ' (ρ(h⁻¹) ρ(t⁻¹) w)`. Hence `h⁻¹ ∈ S_t` and
  `g = (t h) z ∈ C Z`.
- `hasCompactSmoothDualCoefficients_of_support_of_isCompact_center` (compact centre).
  If `Z` is compact, some compact open `K₀` exists, and the support condition above
  holds, then `ρ` has compact coefficients. Proof: as before,
  `support (g ↦ ℓ (ρ g v)) ⊆ C⁻¹ Z`, and `C⁻¹ Z` is compact.

Compact support is concluded with `HasCompactSupport.intro`, which needs `R1Space`.
Topological groups are regular, hence `R1`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Compact.CompactRepresentationCoefficientCriterionProof` | `hasCompactSupport_projectedOrbit`, `HasCompactSmoothDualCoefficients` |
| `Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional` | `CompactCoefficientClass.apply_heckeAction_normalizedIndicator` |
| `Langlands.Representation.Hecke.ActionProjection` | `Hecke.fixedProjection`, `Hecke.fixedProjection_apply` |
| `Langlands.Representation.Plancherel.RationalNormKernelCentralCover` | `isCompact_subgroup_central_coset` |
| `Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof` | `isSmoothVector_restrict_open_iff` |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | `isSmooth_comp` |
| `Mathlib.MeasureTheory.Measure.Haar.Basic` | Haar measure |
