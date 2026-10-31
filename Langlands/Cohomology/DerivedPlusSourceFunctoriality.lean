import Langlands.Cohomology.DerivedPlusSource

/-! # Resolution formulas for derived source squares with target coefficients -/

noncomputable section

namespace Langlands.Cohomology.DerivedPlusSource

open CategoryTheory CategoryTheory.Limits
open DerivedPlus

universe uC vC uD vD uE vE wC wD wE

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [EnoughInjectives D]
variable {E : Type uE} [Category.{vE} E] [Abelian E]
  [HasDerivedCategory.{wE} E]
variable (F : C ⥤ E) [F.Additive] (T : C ⥤ D) [T.Additive]
  [T.PreservesHomology] [T.PreservesInjectiveObjects] (G : D ⥤ E) [G.Additive]
  (τ : F ⟶ T ⋙ G)

set_option backward.isDefEq.respectTransparency false in
/-- The derived source square followed by a coefficient map is computed by any
compatible map from the mapped source resolution to a target resolution. -/
theorem derivedMap_comp_map_ofResolutions {X : C} {Y : D} (α : T.obj X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : InjectiveResolution.Hom (DerivedComparison.mapInjectiveResolution T I) J α) :
    (derivedMap F T G τ).app X ≫ (derivedComplex G).map α =
      (imageResolutionIso F I).hom ≫
        DerivedCategory.Plus.Q.map
          (imageResolutionSquare F T G τ I ≫ imageResolutionMap G φ) ≫
            (imageResolutionIso G J).inv := by
  rw [derivedMap_app F T G τ I]
  apply (cancel_mono (imageResolutionIso G J).hom).1
  simp only [derivedMapOfResolution, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [imageResolutionIso_hom_naturality G φ]
  simp only [Iso.inv_hom_id_assoc]
  rw [Functor.map_comp]

end Langlands.Cohomology.DerivedPlusSource
