import Langlands.Representation.Compact.CompactRepresentationCoefficientCriterionProof
import Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Compactness modulo the centre on an open subgroup

Generic topological-group lemmas for Renard VI.2.1, second Remarks: the comparison of
compact support modulo the centre `Z` with compact support on an open normal subgroup `N`
such that `N ∩ Z` is compact and `N Z` has finite index.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.SupercuspidalRemarks

universe uΓ uV

section Group

variable {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- A compact set is covered by finitely many left cosets of an open subgroup. -/
theorem exists_finset_cosets_cover (N : Subgroup Γ) (hN : IsOpen (N : Set Γ))
    {C : Set Γ} (hC : IsCompact C) :
    ∃ T : Finset Γ, C ⊆ ⋃ t ∈ T, (fun h => t * h) '' (N : Set Γ) := by
  have hcov : C ⊆ ⋃ g : Γ, (fun h => g * h) '' (N : Set Γ) := fun c _ =>
    Set.mem_iUnion.mpr ⟨c, 1, N.one_mem, mul_one c⟩
  exact hC.elim_finite_subcover _ (fun g => (Homeomorph.mulLeft g).isOpenMap _ hN) hcov

/-- An open subgroup meeting the centre in a compact set meets every set that is compact
modulo the centre inside a compact set. -/
theorem exists_isCompact_inter_mul_center (N : Subgroup Γ) (hN : IsOpen (N : Set Γ))
    (hNZ : IsCompact ((N ⊓ Subgroup.center Γ : Subgroup Γ) : Set Γ))
    {C : Set Γ} (hC : IsCompact C) :
    ∃ D : Set Γ, IsCompact D ∧
      (N : Set Γ) ∩ (C * (Subgroup.center Γ : Set Γ)) ⊆ D := by
  obtain ⟨T, hT⟩ := exists_finset_cosets_cover N hN hC
  let E : Set Γ := ⋃ t ∈ T, (fun g => t⁻¹ * g) ''
    {g : Γ | g ∈ N ∧ ∃ z ∈ Subgroup.center Γ, g = t * z}
  have hE : IsCompact E := T.finite_toSet.isCompact_biUnion fun t _ =>
    (isCompact_subgroup_central_coset N hNZ t).image (continuous_const.mul continuous_id)
  refine ⟨C * E, hC.mul hE, ?_⟩
  rintro x ⟨hxN, c, hc, z, hz, rfl⟩
  obtain ⟨t, ht, hct⟩ := Set.mem_iUnion₂.mp (hT hc)
  obtain ⟨h, hh, rfl⟩ := hct
  refine ⟨t * h, hc, z, Set.mem_iUnion₂.mpr ⟨t, ht, t * z, ⟨?_, z, hz, rfl⟩, ?_⟩, rfl⟩
  · have hcomm : h * z = z * h := (Subgroup.mem_center_iff.mp hz h)
    have hmem := N.mul_mem hxN (N.inv_mem hh)
    have heq : t * h * z * h⁻¹ = t * z := by
      rw [mul_assoc t h z, hcomm, ← mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [heq] using hmem
  · simp

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- If `N ⊔ Z` has finite index, every element is `t * h * z` with `t` in a fixed finite
set, `h ∈ N` and `z` central. -/
theorem exists_finset_mul_mul_center (N : Subgroup Γ) [N.Normal]
    [(N ⊔ Subgroup.center Γ).FiniteIndex] :
    ∃ T : Finset Γ, ∀ g : Γ, ∃ t ∈ T, ∃ h ∈ N, ∃ z ∈ Subgroup.center Γ, g = t * h * z := by
  classical
  let L := N ⊔ Subgroup.center Γ
  let := Fintype.ofFinite (Γ ⧸ L)
  refine ⟨Finset.univ.image fun q : Γ ⧸ L => q.out, fun g => ?_⟩
  obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L g
  have hl' : (l⁻¹ : Γ) ∈ ((L : Subgroup Γ) : Set Γ) := L.inv_mem l.property
  rw [Subgroup.normal_mul] at hl'
  obtain ⟨h, hh, z, hz, hhz⟩ := hl'
  refine ⟨(QuotientGroup.mk g : Γ ⧸ L).out, Finset.mem_image_of_mem _ (Finset.mem_univ _),
    h, hh, z, hz, ?_⟩
  change h * z = (l : Γ)⁻¹ at hhz
  rw [mul_assoc, hhz, hl, mul_assoc, mul_inv_cancel, mul_one]

end Group

section Representation

variable {Γ : Type uΓ} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

omit [IsTopologicalGroup Γ] in
/-- A smooth vector of the algebraic dual action is invariant under an open subgroup. -/
theorem exists_openSubgroup_invariant_of_isSmoothVector_dual
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    {ℓ : Module.Dual ℂ V} (hℓ : IsSmoothVector ρ.dual ℓ) :
    ∃ L : OpenSubgroup Γ, ∀ k ∈ L, ∀ y : V, ℓ (ρ k y) = ℓ y := by
  obtain ⟨L, hL⟩ := hℓ
  refine ⟨L, fun k hk y => ?_⟩
  have heq := congrArg (fun f : Module.Dual ℂ V => f y) (hL ⟨k⁻¹, L.inv_mem hk⟩)
  change ℓ (ρ (k⁻¹)⁻¹ y) = ℓ y at heq
  simpa only [inv_inv] using heq

/-- **Uniform support (IV.1.3).** If all smooth coefficients of a smooth representation
have compact support, then for each compact open `K` and each vector `w` the coefficients
`h ↦ ℓ (ρ h w)` of all `K`-invariant linear forms `ℓ` are supported in one compact set. -/
theorem exists_isCompact_uniform_support [LocallyCompactSpace Γ]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (hs : IsSmooth ρ) (hc : HasCompactSmoothDualCoefficients ρ)
    (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ)) (w : V) :
    ∃ S : Set Γ, IsCompact S ∧ ∀ ℓ : Module.Dual ℂ V, (∀ k ∈ K, ∀ y : V, ℓ (ρ k y) = ℓ y) →
      Function.support (fun h : Γ => ℓ (ρ h w)) ⊆ S := by
  borelize Γ
  let μ : Measure Γ := Measure.haar
  refine ⟨tsupport (fun h : Γ => Hecke.fixedProjection μ ρ hs K hK (ρ h w)),
    Renard.CompactRepresentation.hasCompactSupport_projectedOrbit μ ρ hs hc K hK w, ?_⟩
  intro ℓ hℓ h hh
  apply subset_tsupport
  intro h0
  apply hh
  show ℓ (ρ h w) = 0
  have hinv := CompactCoefficientClass.apply_heckeAction_normalizedIndicator μ ρ hs K hK hℓ
    (ρ h w)
  change Hecke.fixedProjection μ ρ hs K hK (ρ h w) = 0 at h0
  rw [← hinv, ← Hecke.fixedProjection_apply, h0]
  simp

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- If `g⁻¹ ∈ C Z` with `Z` the centre, then `g ∈ C⁻¹ Z`. -/
theorem mem_inv_mul_center {C : Set Γ} {g : Γ}
    (hg : g⁻¹ ∈ C * (Subgroup.center Γ : Set Γ)) :
    g ∈ C⁻¹ * (Subgroup.center Γ : Set Γ) := by
  obtain ⟨c, hc, z, hz, hcz⟩ := hg
  refine ⟨c⁻¹, by simpa using hc, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
  have hg' : g = (c * z)⁻¹ := by rw [show c * z = g⁻¹ from hcz, inv_inv]
  rw [hg', mul_inv_rev]
  exact Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) c⁻¹

/-- A smooth vector of the algebraic dual is invariant under a compact open subgroup,
namely its invariance group intersected with a given compact open subgroup `K₀`. -/
theorem exists_compact_invariant_of_isSmoothVector_dual
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    {ℓ : Module.Dual ℂ V} (hℓ : IsSmoothVector ρ.dual ℓ)
    (K₀ : OpenSubgroup Γ) (hK₀ : IsCompact (K₀ : Set Γ)) :
    ∃ K : OpenSubgroup Γ, IsCompact (K : Set Γ) ∧ ∀ x ∈ K, ∀ y : V, ℓ (ρ x y) = ℓ y := by
  obtain ⟨L, hL⟩ := exists_openSubgroup_invariant_of_isSmoothVector_dual ρ hℓ
  refine ⟨K₀ ⊓ L, ?_, fun x hx y => hL x (OpenSubgroup.mem_inf.mp hx).2 y⟩
  rw [OpenSubgroup.coe_inf]
  exact hK₀.inter_right L.isClosed

/-- Restriction to an open subgroup preserves compactness of all coefficients against
smooth vectors of the dual. -/
theorem hasCompactSmoothDualCoefficients_comp_openSubgroup
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (H : OpenSubgroup Γ) (hc : HasCompactSmoothDualCoefficients ρ) :
    HasCompactSmoothDualCoefficients (ρ.comp H.toSubgroup.subtype) := by
  intro v ℓ hℓ
  have hℓ' : IsSmoothVector ρ.dual ℓ := (isSmoothVector_restrict_open_iff ρ.dual H ℓ).mp hℓ
  have hcl : IsClosed (H.toSubgroup : Set Γ) := H.isClosed
  exact (hc v ℓ hℓ').comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal

/-- **Compact modulo the centre implies compact on an open subgroup.** Let `H` be an open
subgroup with `H ∩ Z` compact. If for every compact open `K` and every `w` the coefficients
`g ↦ ℓ (ρ g⁻¹ w)` of the `K`-invariant forms `ℓ` are all supported in `C Z` for one compact
`C`, then the restriction of `ρ` to `H` has compact coefficients against smooth dual
vectors. -/
theorem hasCompactSmoothDualCoefficients_comp_of_support
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (H : OpenSubgroup Γ)
    (hHZ : IsCompact ((H.toSubgroup ⊓ Subgroup.center Γ : Subgroup Γ) : Set Γ))
    (K₀ : OpenSubgroup Γ) (hK₀ : IsCompact (K₀ : Set Γ))
    (hsupp : ∀ K : OpenSubgroup Γ, IsCompact (K : Set Γ) → ∀ w : V,
      ∃ C : Set Γ, IsCompact C ∧ ∀ ℓ : Module.Dual ℂ V, (∀ x ∈ K, ∀ y : V, ℓ (ρ x y) = ℓ y) →
        Function.support (fun g : Γ => ℓ (ρ g⁻¹ w)) ⊆ C * (Subgroup.center Γ : Set Γ)) :
    HasCompactSmoothDualCoefficients (ρ.comp H.toSubgroup.subtype) := by
  intro v ℓ hℓ
  have hℓ' : IsSmoothVector ρ.dual ℓ := (isSmoothVector_restrict_open_iff ρ.dual H ℓ).mp hℓ
  obtain ⟨K, hK, hKinv⟩ := exists_compact_invariant_of_isSmoothVector_dual ρ hℓ' K₀ hK₀
  obtain ⟨C, hC, hCsupp⟩ := hsupp K hK v
  obtain ⟨D, hD, hND⟩ := exists_isCompact_inter_mul_center H.toSubgroup H.isOpen hHZ hC.inv
  have hcl : IsClosed (H.toSubgroup : Set Γ) := H.isClosed
  have hemb := hcl.isClosedEmbedding_subtypeVal
  refine HasCompactSupport.intro (hemb.isCompact_preimage hD) ?_
  intro h hh
  by_contra hne
  apply hh
  apply hND
  refine ⟨h.property, mem_inv_mul_center (hCsupp ℓ hKinv ?_)⟩
  change ℓ (ρ ((h : Γ)⁻¹)⁻¹ v) ≠ 0
  rw [inv_inv]
  exact hne

/-- **Compact on an open subgroup implies compact modulo the centre, uniformly.** Let `H`
be an open normal subgroup such that `H Z` has finite index. If the restriction of a smooth
`ρ` to `H` has compact coefficients against smooth dual vectors, then for each compact open
`K` and each `w` there is one compact `C` such that every `K`-invariant form `ℓ` has
`g ↦ ℓ (ρ g⁻¹ w)` supported in `C Z`. -/
theorem support_subset_mul_center_of_comp [LocallyCompactSpace Γ]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (hs : IsSmooth ρ)
    (H : OpenSubgroup Γ) [H.toSubgroup.Normal]
    [(H.toSubgroup ⊔ Subgroup.center Γ).FiniteIndex]
    (hc : HasCompactSmoothDualCoefficients (ρ.comp H.toSubgroup.subtype))
    (K : OpenSubgroup Γ) (hK : IsCompact (K : Set Γ)) (w : V) :
    ∃ C : Set Γ, IsCompact C ∧ ∀ ℓ : Module.Dual ℂ V, (∀ x ∈ K, ∀ y : V, ℓ (ρ x y) = ℓ y) →
      Function.support (fun g : Γ => ℓ (ρ g⁻¹ w)) ⊆ C * (Subgroup.center Γ : Set Γ) := by
  classical
  let σ : Representation ℂ H.toSubgroup V := ρ.comp H.toSubgroup.subtype
  have hσ : IsSmooth σ := isSmooth_comp H.toSubgroup.subtype continuous_subtype_val hs
  have hcl : IsClosed (H.toSubgroup : Set Γ) := H.isClosed
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace H.toSubgroup := hemb.locallyCompactSpace
  let K' : OpenSubgroup H.toSubgroup :=
    OpenSubgroup.comap H.toSubgroup.subtype continuous_subtype_val K
  have hK' : IsCompact (K' : Set H.toSubgroup) := hemb.isCompact_preimage hK
  obtain ⟨T, hT⟩ := exists_finset_mul_mul_center H.toSubgroup
  have hS : ∀ t : Γ, ∃ S : Set H.toSubgroup, IsCompact S ∧
      ∀ ℓ : Module.Dual ℂ V, (∀ k ∈ K', ∀ y : V, ℓ (σ k y) = ℓ y) →
        Function.support (fun h : H.toSubgroup => ℓ (σ h (ρ t⁻¹ w))) ⊆ S :=
    fun t => exists_isCompact_uniform_support σ hσ hc K' hK' (ρ t⁻¹ w)
  choose S hS hSsupp using hS
  refine ⟨⋃ t ∈ T, (fun s : H.toSubgroup => t * (s : Γ)⁻¹) '' S t,
    T.finite_toSet.isCompact_biUnion fun t _ =>
      (hS t).image (continuous_const.mul continuous_subtype_val.inv), ?_⟩
  intro ℓ hℓ g hg
  obtain ⟨t, ht, h, hh, z, hz, rfl⟩ := hT g
  let ℓ' : Module.Dual ℂ V := ℓ ∘ₗ ρ z⁻¹
  have hzc : ∀ x : Γ, x * z⁻¹ = z⁻¹ * x :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz)
  have hℓ' : ∀ k ∈ K', ∀ y : V, ℓ' (σ k y) = ℓ' y := by
    intro k hk y
    change ℓ (ρ z⁻¹ (ρ (k : Γ) y)) = ℓ (ρ z⁻¹ y)
    rw [← Module.End.mul_apply, ← map_mul, ← hzc, map_mul, Module.End.mul_apply]
    exact hℓ (k : Γ) (OpenSubgroup.mem_comap.mp hk) _
  have hmem : (⟨h, hh⟩ : H.toSubgroup)⁻¹ ∈ S t := by
    apply hSsupp t ℓ' hℓ'
    change ℓ (ρ z⁻¹ (ρ h⁻¹ (ρ t⁻¹ w))) ≠ 0
    have hg' : ℓ (ρ (t * h * z)⁻¹ w) ≠ 0 := hg
    simpa only [mul_inv_rev, map_mul, Module.End.mul_apply] using hg'
  refine ⟨t * h, Set.mem_iUnion₂.mpr ⟨t, ht, ⟨h, hh⟩⁻¹, hmem, ?_⟩, z, hz, rfl⟩
  simp

/-- **Compact centre.** If the centre `Z` is compact and every `g ↦ ℓ (ρ g⁻¹ w)` (for
`K`-invariant `ℓ`) is supported in `C Z` with `C` compact depending on `K` and `w`, then
all coefficients of `ρ` against smooth dual vectors have compact support. -/
theorem hasCompactSmoothDualCoefficients_of_support_of_isCompact_center
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (hZ : IsCompact (Subgroup.center Γ : Set Γ))
    (K₀ : OpenSubgroup Γ) (hK₀ : IsCompact (K₀ : Set Γ))
    (hsupp : ∀ K : OpenSubgroup Γ, IsCompact (K : Set Γ) → ∀ w : V,
      ∃ C : Set Γ, IsCompact C ∧ ∀ ℓ : Module.Dual ℂ V, (∀ x ∈ K, ∀ y : V, ℓ (ρ x y) = ℓ y) →
        Function.support (fun g : Γ => ℓ (ρ g⁻¹ w)) ⊆ C * (Subgroup.center Γ : Set Γ)) :
    HasCompactSmoothDualCoefficients ρ := by
  intro v ℓ hℓ
  obtain ⟨K, hK, hKinv⟩ := exists_compact_invariant_of_isSmoothVector_dual ρ hℓ K₀ hK₀
  obtain ⟨C, hC, hCsupp⟩ := hsupp K hK v
  refine HasCompactSupport.intro (hC.inv.mul hZ) ?_
  intro g hg
  by_contra hne
  apply hg
  refine mem_inv_mul_center (hCsupp ℓ hKinv ?_)
  change ℓ (ρ g⁻¹⁻¹ v) ≠ 0
  rw [inv_inv]
  exact hne

end Representation

end Langlands.SupercuspidalRemarks
