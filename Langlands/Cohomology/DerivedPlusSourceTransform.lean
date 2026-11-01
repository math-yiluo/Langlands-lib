import Langlands.Cohomology.DerivedPlusSourceFunctoriality

/-! # Transport of derived source squares along natural transformations -/

noncomputable section

namespace Langlands.Cohomology.DerivedPlusSource

open CategoryTheory CategoryTheory.Limits
open DerivedPlus

universe uC vC uD vD uE vE wC wD wE

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable (T U : C ⥤ D) [T.Additive] [U.Additive]
  [T.PreservesHomology] [T.PreservesInjectiveObjects]
  [U.PreservesHomology] [U.PreservesInjectiveObjects] (θ : T ⟶ U)

/-- A natural transformation gives the actual compatible map between the two
mapped injective resolutions, lifting its component at the resolved object. -/
def mapResolutionNatTrans {X : C} (I : InjectiveResolution X) :
    InjectiveResolution.Hom (DerivedComparison.mapInjectiveResolution T I)
      (DerivedComparison.mapInjectiveResolution U I) (θ.app X) where
  hom := (NatTrans.mapHomologicalComplex θ (.up ℕ)).app I.cocomplex
  ι_f_zero_comp_hom_f_zero := by
    rw [CochainComplex.single₀_map_f_zero,
      DerivedComparison.mapInjectiveResolution_ι_f_zero,
      DerivedComparison.mapInjectiveResolution_ι_f_zero]
    exact θ.naturality (I.ι.f 0)

variable {E : Type uE} [Category.{vE} E] [Abelian E]
  (F : C ⥤ E) [F.Additive] (G : D ⥤ E) [G.Additive]
  (τ : F ⟶ T ⋙ G)

/-- Extending the original square and then the actual resolution map equals
extending the square transported by the given natural transformation. -/
theorem imageResolutionSquare_comp_natTrans {X : C} (I : InjectiveResolution X) :
    imageResolutionSquare F T G τ I ≫
      imageResolutionMap G (mapResolutionNatTrans T U θ I) =
    imageResolutionSquare F U G (τ ≫ Functor.whiskerRight θ G) I := by
  apply (CochainComplex.Plus.ι E).map_injective
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
    HomologicalComplex.extendMap _ _
  rw [← HomologicalComplex.extendMap_comp]
  apply congrArg (HomologicalComplex.extendMap · ComplexShape.embeddingUpNat)
  apply HomologicalComplex.hom_ext
  intro n
  rfl

variable [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  [HasDerivedCategory.{wD} D] [EnoughInjectives D] [HasDerivedCategory.{wE} E]

set_option backward.isDefEq.respectTransparency false in
/-- The actual derived source-square construction commutes with transport
along any natural transformation of the source functors. -/
theorem derivedMap_whiskerRight :
    derivedMap F T G τ ≫ Functor.whiskerRight θ (derivedComplex G) =
      derivedMap F U G (τ ≫ Functor.whiskerRight θ G) := by
  apply NatTrans.ext
  funext X
  let I := injectiveResolution X
  change (derivedMap F T G τ).app X ≫ (derivedComplex G).map (θ.app X) = _
  rw [derivedMap_comp_map_ofResolutions F T G τ (θ.app X) I
    (DerivedComparison.mapInjectiveResolution U I) (mapResolutionNatTrans T U θ I),
    imageResolutionSquare_comp_natTrans]
  exact (derivedMap_app F U G (τ ≫ Functor.whiskerRight θ G) I).symm

end Langlands.Cohomology.DerivedPlusSource
