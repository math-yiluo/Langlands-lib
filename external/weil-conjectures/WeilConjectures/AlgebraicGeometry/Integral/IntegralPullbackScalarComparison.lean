/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Scalar normalization of ordinary integral pullback

## References

* Stacks Tags 03D3 and 03D8, inverse image adjunction and composition
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

private def pullbackScalarIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModulePullback f R S c ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom) ≅
        proEtaleModuleInverseImage f R := by
  let e := proEtaleScalarEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  let adj := (proEtaleModuleInverseImageAdjunction f R).comp e.symm.toAdjunction
  have q : e.functor ⋙
      proEtaleRingModuleDirectImage f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleRingModuleDirectImage f R S c := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
    · intro M N b
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      rfl
  let z := adj.ofNatIsoRight q
  let w := (proEtaleRingModulePullbackAdjunction f R S c).leftAdjointUniq z
  exact Functor.isoWhiskerRight w _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.counitIso ≪≫
      Functor.rightUnitor _

attribute [local irreducible] pullbackScalarIso

private def rawPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage f R := by
  let e := pullbackScalarIso f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)
  exact e

attribute [local irreducible] rawPullbackIso

private def derivedPullbackScalarIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingDerivedPullback f R S c ⋙
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).mapDerivedCategory ≅
        adicTowerPullback f R := by
  let e := proEtaleScalarEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)
  let F := proEtaleRingModulePullback f R S c
  let G := e.functor
  have : G.IsEquivalence := inferInstance
  have : G.Additive := inferInstanceAs
    (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).Additive
  let H := proEtaleRingModulePullback f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)
  let ei : F ⋙ G ≅ H := pullbackScalarIso f R S c ≪≫ (rawPullbackIso f R).symm
  exact Functor.mapDerivedCategoryCompIso F G ≪≫
    Functor.mapDerivedCategoryNatIso ei


/-- Derived pullback, after scalar normalization, is the raw inverse image. -/
theorem proEtaleRingDerivedPullback_scalarComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    Nonempty (proEtaleRingDerivedPullback f R S c ⋙
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).mapDerivedCategory ≅
        adicTowerPullback f R) := by
  exact ⟨derivedPullbackScalarIso f R S c⟩

private def scalarEquivalence {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R := by
  let : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J := by
    change (𝟭 C).IsContinuous _ _
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J := by
    change (𝟭 C).IsContinuous _ _
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := J) (K := J) (S := R) (R := S)
    (CategoryTheory.Equivalence.refl (C := C)) c.hom c.inv
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [S.obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) c.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [R.obj.map_id, Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) c.hom_inv_id)

private def scalarOverIso {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}}
    (c : R ≅ S) (V : C) :
    SheafOfModules.restrictScalars c.hom ⋙ SheafOfModules.overFunctor R V ≅
      SheafOfModules.overFunctor S V ⋙ SheafOfModules.restrictScalars
        (((J.overPullback RingCat.{u + 1} V).mapIso c).hom) := Iso.refl _

attribute [local irreducible] scalarOverIso

private def localScalar {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (g : X ⟶ Y) (V : X.ProEt) :=
  scalarEquivalence ((ProEt.topology X).over V)
    (((ProEt.topology X).overPullback RingCat.{u + 1} V).mapIso
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (d.integralRingIso g)))

private instance localScalar_additive {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (g : X ⟶ Y) (V : X.ProEt) :
    (localScalar d g V).functor.Additive := inferInstanceAs
      (SheafOfModules.restrictScalars _).Additive

end AlgebraicGeometry.Scheme
