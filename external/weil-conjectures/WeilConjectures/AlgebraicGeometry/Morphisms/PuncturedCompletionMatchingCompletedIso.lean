/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapInjective
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapSurjective

/-! # The completed comparison for matching sections

## References

* Stacks Project, Tag 0BLH, via Tags 05ER and 05EU
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed comparison for matching sections. -/
theorem completedMap_isIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    IsIso D.completedMap := by
  have hbij : Function.Bijective D.completedRingMap :=
    ⟨D.completedRingMap_injective hU, D.completedRingMap_surjective hU⟩
  have : IsIso D.completedRingMap :=
    (ConcreteCategory.isIso_iff_bijective D.completedRingMap).mpr hbij
  have : IsAffine E := isAffine_of_isAffineHom s
  let H := isPullback_SpecMap_pushout D.baseMap (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
  have heq : D.completedMap = E.toSpecΓ ≫ Spec.map D.completedRingMap ≫
      H.isoPullback.hom := by
    simp only [completedMap, modelMap, completionSpecMap]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc,
        H.isoPullback_hom_fst]
      rw [← Spec.map_comp]
      simp only [completedRingMap, pushout.inl_desc]
      rfl
    · simp only [pullback.lift_snd, Category.assoc,
        H.isoPullback_hom_snd]
      rw [← Spec.map_comp]
      simp only [completedRingMap, pushout.inr_desc]
      rw [Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [heq]
  infer_instance

end AlgebraicGeometry.Scheme.CompletionGluingData
