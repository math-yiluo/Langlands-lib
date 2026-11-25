/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.Ring.Limits

/-! # The explicit ring of matching punctured and completed sections

## References

* Stacks Project, Tags 0BLH and 05ER (the functor H⁰)
* Stacks Project, Tag 05ER, the construction H⁰
* Stacks Project, Tag 0BLH, set Y = Spec B
* Stacks Project, Tag 05ER, the natural comparison Ψ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The completion map used by the matching-sections construction. -/
noncomputable abbrev completionSpecMap (A : Type u) [CommRing A] [IsLocalRing A] :=
  Spec.map (CommRingCat.ofHom
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))

/-- The given overlap identification, retained as data rather than chosen from a theorem. -/
structure CompletionGluingData (A : Type u) [CommRing A] [IsLocalRing A]
    (U : (Spec (.of A)).Opens) {Y : Scheme.{u}} (q : Y ⟶ U.toScheme)
    (E : Scheme.{u}) (s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))) where
  overlapIso : pullback q (completionSpecMap A ∣_ U) ≅
    (s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).toScheme
  over : overlapIso.hom ≫ s ∣_ (completionSpecMap A ⁻¹ᵁ U) =
    pullback.snd q (completionSpecMap A ∣_ U)

namespace CompletionGluingData
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
variable {E : Scheme.{u}} {s : E ⟶ Spec
  (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
variable (D : CompletionGluingData A U q E s)

/-- Map from the overlap to the completed model. -/
noncomputable def toCompleted : pullback q (completionSpecMap A ∣_ U) ⟶ E :=
  D.overlapIso.hom ≫ (s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).ι

/-- The two overlap maps agree over the original affine base. -/
theorem overlap_base :
    pullback.fst q (completionSpecMap A ∣_ U) ≫ (q ≫ U.ι) =
      D.toCompleted ≫ (s ≫ completionSpecMap A) := by
  simp only [toCompleted, Category.assoc]
  rw [← morphismRestrict_ι_assoc, ← morphismRestrict_ι,
    ← Category.assoc D.overlapIso.hom (s ∣_ _), D.over,
    ← pullback.condition_assoc]

/-- The actual ring of pairs of sections agreeing on the overlap. -/
noncomputable def matchingRing : CommRingCat.{u} :=
  pullback (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop

/-- The base-ring map into the ring of matching sections. -/
noncomputable def baseMap : CommRingCat.of A ⟶ D.matchingRing :=
  (ΓSpecIso (.of A)).inv ≫ pullback.lift (q ≫ U.ι).appTop
    (s ≫ completionSpecMap A).appTop (by
      simpa only [Hom.comp_appTop] using congrArg Hom.appTop D.overlap_base)

/-- The explicit affine candidate, without any finiteness assertion. -/
noncomputable def model : Scheme.{u} := Spec D.matchingRing

/-- Its structural map to the original base. -/
noncomputable def modelMap : D.model ⟶ Spec (.of A) := Spec.map D.baseMap

/-- The map from the punctured model induced by the first projection of matching sections. -/
noncomputable def fromPunctured : Y ⟶ D.model :=
  Y.toSpecΓ ≫ Spec.map (pullback.fst
    (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop)

/-- The first comparison is a morphism over Spec A. -/
theorem fromPunctured_modelMap : D.fromPunctured ≫ D.modelMap = q ≫ U.ι := by
  simp only [fromPunctured, modelMap, baseMap, Category.assoc, ← Spec.map_comp,
    pullback.lift_fst]
  rw [Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The map from the completed model induced by the second projection of matching sections. -/
noncomputable def fromCompleted : E ⟶ D.model :=
  E.toSpecΓ ≫ Spec.map (pullback.snd
    (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop)

/-- The second comparison is a morphism over Spec A. -/
theorem fromCompleted_modelMap : D.fromCompleted ≫ D.modelMap =
    s ≫ completionSpecMap A := by
  simp only [fromCompleted, modelMap, baseMap, Category.assoc, ← Spec.map_comp,
    pullback.lift_snd]
  rw [Spec.map_comp, ← Category.assoc, ← toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The canonical comparison with the punctured restriction of the explicit candidate. -/
noncomputable def puncturedMap : Y ⟶ (D.modelMap ⁻¹ᵁ U).toScheme :=
  pullback.lift D.fromPunctured q D.fromPunctured_modelMap ≫
    (pullbackRestrictIsoRestrict D.modelMap U).hom

/-- Compatibility of the punctured comparison with its base map. -/
theorem puncturedMap_over : D.puncturedMap ≫ D.modelMap ∣_ U = q := by
  simp [puncturedMap]

/-- The canonical comparison with the completed base change of the explicit candidate. -/
noncomputable def completedMap : E ⟶ pullback D.modelMap (completionSpecMap A) :=
  pullback.lift D.fromCompleted s D.fromCompleted_modelMap

/-- Compatibility of the completed comparison with its base map. -/
theorem completedMap_over : D.completedMap ≫
    pullback.snd D.modelMap (completionSpecMap A) = s := by
  simp [completedMap]

end CompletionGluingData
end AlgebraicGeometry.Scheme
