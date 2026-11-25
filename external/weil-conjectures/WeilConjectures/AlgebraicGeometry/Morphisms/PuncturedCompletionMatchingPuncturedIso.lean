/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingAffineSections

/-! # The punctured comparison for matching sections

## References

* Stacks Project, Tag 0BLH, via Tags 05ER and 05EU
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The punctured comparison for matching sections. -/
theorem puncturedMap_isIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    IsIso D.puncturedMap := by
  have : IsAffineHom D.modelMap := by
    change IsAffineHom (Spec.map D.baseMap)
    infer_instance
  let r := D.modelMap ∣_ U
  have : IsAffineHom r :=
    IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) ‹IsAffineHom D.modelMap› U
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨_, ⟨f, rfl⟩, hxf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen
      (U.ι (r x)) (r x).2
  let V := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f
  let W := r ⁻¹ᵁ V
  have hV : IsAffineOpen V :=
    (IsAffineOpen.Spec_basicOpen f).preimage_of_isOpenImmersion U.ι
      (by rw [Opens.opensRange_ι]; exact hf)
  have hW : IsAffineOpen W := hV.preimage r
  refine ⟨W, hxf, ?_⟩
  have hsource : IsAffineOpen (D.puncturedMap ⁻¹ᵁ W) := by
    have heq : D.puncturedMap ⁻¹ᵁ W = q ⁻¹ᵁ V := by
      change D.puncturedMap ⁻¹ᵁ (r ⁻¹ᵁ V) = _
      rw [← Hom.comp_preimage, D.puncturedMap_over]
    rw [heq]
    exact hV.preimage q
  have : IsAffine W.toScheme := hW
  have : IsAffine (D.puncturedMap ⁻¹ᵁ W).toScheme := hsource
  have : IsIso (D.puncturedMap ∣_ W).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (D.puncturedMap_basicOpen_appTop_bijective hU f hf)
  exact (HasAffineProperty.iff_of_isAffine
    (P := MorphismProperty.isomorphisms Scheme)).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
