/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities

/-!
# Ordinary scalar balancing commutes with pullback

## References

* Stacks Project, Tags 07A4 and 07A7
* Stacks 03EK
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints
attribute [local irreducible] upperStar
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private noncomputable instance extensionOplax
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private instance extensionAdjMonoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T).IsMonoidal :=
  isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private instance extensionDeltaIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (Functor.OplaxMonoidal.δ (ProEtale.etaleSheafExtendScalars φ T) M N) :=
  isIso_δ_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) M N

private instance extensionEtaIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    IsIso (Functor.OplaxMonoidal.η (ProEtale.etaleSheafExtendScalars φ T)) :=
  isIso_η_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private noncomputable instance extensionMonoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).Monoidal := .ofOplaxMonoidal _

/-- The balancing map is an isomorphism without a flatness hypothesis. -/
theorem scalarSheafTensorMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (scalarSheafTensorMap φ T M) := by
  let := φ.toAlgebra
  have : T.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  exact isIso_sheafAdjunction_unitProjection T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (algebraMap A B)) M

/-- The ordinary coefficient iso used in the derived coefficient identification. -/
def scalarCoefficientSheafPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (upperStar (ModuleCat.{u + 1} A) f).obj (scalarCoefficientSheaf φ W) ≅
      scalarCoefficientSheaf φ Z :=
  (upperStarRestrictScalarsIsoSheaf φ f).app (𝟙_ _) ≪≫
    (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
      (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) f)).symm

private theorem ordinary_reverse_of_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {sx : A ⥤ B} {rx : B ⥤ A} (ax : sx ⊣ rx)
    {st : C ⥤ D} {rt : D ⥤ C} (at' : st ⊣ rt)
    {f : A ⥤ C} {rf : C ⥤ A} (af : f ⊣ rf)
    {g : B ⥤ D} {rg : D ⥤ B} (ag : g ⊣ rg)
    (e : rx ⋙ f ≅ g ⋙ rt) (δ : rg ⋙ rx ≅ rt ⋙ rf)
    (hδ : (mateEquiv ag af (TwoSquare.mk _ _ _ _ e.hom)) = δ.hom) :
    ((mateEquiv ax at').symm (TwoSquare.mk _ _ _ _ e.hom)) =
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv := by
  apply (mateEquiv ax at').injective
  apply (mateEquiv ag af).injective
  rw [Equiv.apply_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  have h := iterated_mateEquiv_conjugateEquiv ax at' af ag
    (TwoSquare.mk _ _ _ _
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv)
  dsimp only [TwoSquare.mk] at h hδ
  rw [h, hδ]
  simp only [conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  erw [Equiv.apply_symm_apply]

private theorem scalarPullback_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
        (ProEtale.etaleSheafExtendScalarsAdjunction φ Z)
        (scalarSheafPullbackIso φ f).inv = (upperStarRestrictScalarsIsoSheaf φ f).hom := by
  have h := ordinary_reverse_of_mate
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ Z)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarRestrictScalarsIsoSheaf φ f) (lowerStarCompRestrictScalarsIso φ f)
    (underived_mate φ f)
  let e := mateEquiv (G := upperStar (ModuleCat.{u + 1} A) f)
    (H := upperStar (ModuleCat.{u + 1} B) f)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ Z)
  have h' : e.symm (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom) =
      TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ f).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact NatTrans.congr_app h M
  have hh := congrArg (fun q ↦ (e q)) h'
  simpa only [Equiv.apply_symm_apply] using hh.symm

private instance scalarPullbackMonoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    NatTrans.IsMonoidal (scalarSheafPullbackIso φ f).hom := by
  have : NatTrans.IsMonoidal (lowerStarCompRestrictScalarsIso φ f).hom := by
    exact Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
      (MorphismProperty.Over.pullback @Etale ⊤ f)
      (W.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)
      (A := ModuleCat.{u + 1} B) (ModuleCat.restrictScalars.{u + 1} φ)
  have : NatTrans.IsMonoidal (lowerStarCompRestrictScalarsIso φ f).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (lowerStarCompRestrictScalarsIso φ f).inv)
  unfold scalarSheafPullbackIso
  exact isMonoidal_conjugateEquiv_symm _ _ _

/-- The scalar balancing square before localization. -/
theorem scalarSheafTensorPullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) f).map (scalarSheafTensorMap φ W M) ≫
        (upperStarRestrictScalarsIsoSheaf φ f).hom.app
          ((ProEtale.etaleSheafExtendScalars φ W).obj M) ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
          ((scalarSheafPullbackIso φ f).hom.app M) =
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) M
          (scalarCoefficientSheaf φ W) ≫
        ((upperStar (ModuleCat.{u + 1} A) f).obj M ◁
          (scalarCoefficientSheafPullbackIso φ f).hom) ≫
        scalarSheafTensorMap φ Z ((upperStar (ModuleCat.{u + 1} A) f).obj M) := by
  have h := (ProEtale.etaleSheafExtendScalarsAdjunction φ W).map_unitProjection_comp_mateEquiv
    (ProEtale.etaleSheafExtendScalarsAdjunction φ Z) (scalarSheafPullbackIso φ f)
    (NatTrans.IsMonoidal.δ_comp_tensorHom _) M
  rw [scalarPullback_mate] at h
  exact h

end AlgebraicGeometry.Etale
