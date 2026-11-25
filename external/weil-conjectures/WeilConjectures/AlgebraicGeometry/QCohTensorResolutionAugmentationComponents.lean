/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAffineModel

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The extended augmentation in degree zero. -/
theorem tensorResolutionAugmentation_f_zero (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    (tensorResolutionAugmentation A M P).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom =
      (P.complex.extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).hom ≫
        P.π.f 0 := by
  dsimp only [tensorResolutionAugmentation, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f P.π ComplexShape.embeddingDownNat
      (i := 0) (i' := 0) rfl,
    HomologicalComplex.extendSingleIso_hom_f]
  simp only [Category.assoc, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]
  erw [Category.comp_id]
  erw [Iso.inv_hom_id, Category.comp_id]

/-- Exact sheafification preserves the normalization of the degree-zero augmentation. -/
theorem tensorResolutionTildeAugmentation_f_zero (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    (tensorResolutionTildeAugmentation A M P).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (tilde (R := .of A) M)).hom =
      tilde.map ((P.complex.extendXIso ComplexShape.embeddingDownNat
        (i := 0) (i' := 0) rfl).hom ≫ P.π.f 0) := by
  dsimp only [tensorResolutionTildeAugmentation, HomologicalComplex.comp_f]
  simp only [Iso.app_hom, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Category.assoc]
  change (tilde.functor (.of A)).map ((tensorResolutionAugmentation A M P).f 0) ≫
    (tilde.functor (.of A)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom = _
  rw [← Functor.map_comp, tensorResolutionAugmentation_f_zero]
  rfl

end AlgebraicGeometry
