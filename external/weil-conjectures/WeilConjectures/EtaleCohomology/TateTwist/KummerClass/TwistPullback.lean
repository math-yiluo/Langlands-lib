/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.Basic

/-!
# Pullback of the identifications of the Tate twist datum

For `f : X ⟶ Y` over `Spec ℤ[1/n]`, the identifications `Λ(1) ≅ (μₙ ⊗ Λ)[0]`
(`AlgebraicGeometry.Etale.tateTwistObjectOneIso`) and `Λ ≅ (Λ ⊗ ℤ)[0]`
(`AlgebraicGeometry.Etale.constantComplexIsoSingleFunctorExtendScalarsInt`) used to define the
Kummer class are compatible with the derived pullback `Lf^*`.

## Main results

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_tateTwistObjectOneIso`
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [HasInvertibleExponent Λ X]
  [NeZero (ringChar Λ)] {Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y)

/-! The unfolding lemmas below restate the definitions of the identifications as composites
elaborated in this file. Rewriting with them, rather than unfolding the definitions, keeps the
instance arguments and the proofs inside these composites syntactically equal to those of the
compatibility lemmas used below, so that the kernel does not have to identify them under
projections. -/

private lemma tateTwistObjectIsoSingleFunctor_eq (Z : Scheme.{u}) [HasInvertibleExponent Λ Z]
    (m : ℤ) :
    tateTwistObjectIsoSingleFunctor Λ Z m =
      eqToIso (congrFun (tateTwistObject_eq Λ Z) m) ≪≫
        L((toInvertibleExponentBase (Λ := Λ) Z)^*[ModuleCat.{u + 1} Λ]).mapIso
          ((tateSheafTensorInverse Λ).zpowSingleFunctorIso m) ≪≫
        (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ)
          (toInvertibleExponentBase (Λ := Λ) Z)).app ((tateSheafTensorInverse Λ).zpow m) :=
  rfl

private lemma tateTwistObjectOneIso_eq (Z : Scheme.{u}) [HasInvertibleExponent Λ Z] :
    tateTwistObjectOneIso Z Λ = tateTwistObjectIsoSingleFunctor Λ Z 1 ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (X := (toInvertibleExponentBase (Λ := Λ) Z)^*[ModuleCat.{u + 1} Λ].obj
          ((tateSheafTensorInverse Λ).zpow 1)) (tateTwistSheafOneIso Z Λ) :=
  rfl

private lemma leftDerivedUpperStarTateTwistObjectIso_eq (m : ℤ) :
    leftDerivedUpperStarTateTwistObjectIso Λ f m =
      L((f)^*[ModuleCat.{u + 1} Λ]).mapIso (eqToIso (congrFun (tateTwistObject_eq Λ Y) m)) ≪≫
        pullbackIntTensorFamilyIso _ _ f _ _ (comp_toInvertibleExponentBase f).symm m ≪≫
        eqToIso (congrFun (tateTwistObject_eq Λ X) m).symm :=
  rfl

/-- The identifications `Λ(1) ≅ μₙ ⊗ Λ` placed in degree zero are compatible with the derived
pullbacks. -/
lemma leftDerivedUpperStar_map_tateTwistObjectOneIso :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateTwistObjectOneIso Y Λ).hom ≫
        (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app (Y.rootsOfUnitySheaf (ringChar Λ)) ≫
              (extendScalars Λ X).map
                (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f)) =
      (leftDerivedUpperStarTateTwistObjectIso Λ f 1).hom ≫ (tateTwistObjectOneIso X Λ).hom := by
  have hπ := (comp_toInvertibleExponentBase (Λ := Λ) f).symm
  have hc : ∀ (πX : X ⟶ invertibleExponentBase.{u} Λ)
      (hπ : πX = f ≫ toInvertibleExponentBase (Λ := Λ) Y),
      (upperStarComp _ f _ πX hπ).hom.app _ ≫
        (f)^*[AddCommGrpCat.{u + 1}].map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf
          (ringChar Λ) (toInvertibleExponentBase (Λ := Λ) Y)) ≫
          upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) f =
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) πX := by
    rintro _ rfl
    exact upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp _ f _
  have hσ := upperStarComp_hom_app_comp_upperStar_map_extendScalars Λ f _ _ hπ _ _ _ (hc _ hπ)
    (ρ_ (tateSheaf Λ (invertibleExponentBase.{u} Λ))).hom
  have hG := leftDerivedUpperStar_map_singleFunctor_comp (ModuleCat.{u + 1} Λ) f _ _ hπ _
    (tateTwistSheafOneIso Y Λ).hom (tateTwistSheafOneIso X Λ).hom _ hσ
  have n := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).inv.naturality
    ((tateSheafTensorInverse Λ).zpowSingleFunctorIso 1).hom
  rw [tateTwistObjectOneIso_eq Λ Y, tateTwistObjectOneIso_eq Λ X,
    tateTwistObjectIsoSingleFunctor_eq Λ Y, tateTwistObjectIsoSingleFunctor_eq Λ X,
    leftDerivedUpperStarTateTwistObjectIso_eq]
  simp only [pullbackIntTensorFamilyIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Functor.comp_map] at hG n ⊢
  erw [← reassoc_of% n]
  rw [hG]

omit [NeZero (ringChar Λ)] in
private lemma constantComplexIsoSingleFunctorExtendScalarsInt_eq (Z : Scheme.{u})
    [HasInvertibleExponent Λ Z] :
    constantComplexIsoSingleFunctorExtendScalarsInt Z Λ =
      (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) Z)).symm ≪≫
        L((toInvertibleExponentBase (Λ := Λ) Z)^*[ModuleCat.{u + 1} Λ]).mapIso
          (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit
            (invertibleExponentBase.{u} Λ) Λ) ≪≫
        (singleFunctorCompLeftDerivedUpperStarIso _ (toInvertibleExponentBase (Λ := Λ) Z)).app
          ((extendScalars Λ (invertibleExponentBase.{u} Λ)).obj
            (invertibleExponentBase.{u} Λ).constantSheafInt) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) Z)) :=
  rfl

omit [NeZero (ringChar Λ)] in
/-- The identifications `Λ ≅ Λ ⊗ ℤ` placed in degree zero are compatible with the derived
pullbacks. -/
lemma leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (constantComplexIsoSingleFunctorExtendScalarsInt Y Λ).hom ≫
        (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ f).hom.app Y.constantSheafInt ≫
              (extendScalars Λ X).map
                ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _)) =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom := by
  have hπ := (comp_toInvertibleExponentBase (Λ := Λ) f).symm
  have hc : ∀ (πX : X ⟶ invertibleExponentBase.{u} Λ)
      (hπ : πX = f ≫ toInvertibleExponentBase (Λ := Λ) Y),
      (upperStarComp _ f _ πX hπ).hom.app _ ≫
        (f)^*[AddCommGrpCat.{u + 1}].map ((upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (toInvertibleExponentBase (Λ := Λ) Y)).hom.app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))) ≫
          (upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app _ =
        (upperStarConstantSheafIso AddCommGrpCat.{u + 1} πX).hom.app _ := by
    rintro _ rfl
    exact upperStarConstantSheafIso_comp _ f _ _
  have hσ := upperStarComp_hom_app_comp_upperStar_map_extendScalars Λ f _ _ hπ
    (BY := Y.constantSheafInt) (BX := X.constantSheafInt) _ _ _ (hc _ hπ)
    (𝟙 ((extendScalars Λ (invertibleExponentBase.{u} Λ)).obj
      (invertibleExponentBase.{u} Λ).constantSheafInt))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hσ
  have hG := leftDerivedUpperStar_map_singleFunctor_comp (ModuleCat.{u + 1} Λ) f _ _ hπ _
    (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) Y)).hom
    (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) X)).hom _ hσ
  have n := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).inv.naturality
    (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit (invertibleExponentBase.{u} Λ) Λ).hom
  have hη : (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
      (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) X)).inv =
      (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) Y)).inv ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).inv.app _ := by
    have c := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) f
      (toInvertibleExponentBase (Λ := Λ) Y) _ hπ
    rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f _ _ hπ).hom.app _ ≫
      (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) Y)).hom)]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    erw [reassoc_of% c]
    exact (leftDerivedUpperStarConstantComplexIso Λ
      (toInvertibleExponentBase (Λ := Λ) X)).hom_inv_id
  rw [constantComplexIsoSingleFunctorExtendScalarsInt_eq Λ Y,
    constantComplexIsoSingleFunctorExtendScalarsInt_eq Λ X]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc, Functor.comp_map] at hG n ⊢
  rw [reassoc_of% hη, ← reassoc_of% n, ← hG]

end Etale

end AlgebraicGeometry
