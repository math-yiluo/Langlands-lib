/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent

import WeilConjectures.CategoryTheory.ConstantInverseImageScalarNormalization
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.CategoryTheory.ConstantRingSectionRigidity
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Hom.InjSurj
import all WeilConjectures.Algebra.Homology.RingedPresentationOnSites.RingedPullbackPresentationOnSitesSupplement
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Constant module inverse image in open-slice coordinates

Source: Stacks Project, Tags 098K, 03D2, 03DI and 00VC; Step 11 of
lem-sf-constant-semilinear-generator-comparison.
(blueprint: lem-sf-constant-open-restriction-model-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale.VaryingRing
namespace AlgebraicGeometry.Scheme

attribute [local instance] openMapContinuous

private instance constantDirectRightAdjoint {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] : (proEtaleConstantModuleDirectImage f A).IsRightAdjoint := by
  unfold proEtaleConstantModuleDirectImage
  exact largePush_isRightAdjoint (ProEt.topology T) (ProEt.topology V)
    (proEtaleBaseChange f) _ _ _

private def modelConstantMap {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] :
    sfCbcModelRing T A ⟶
      ((proEtaleModelBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (proEtaleModelTopology T) (proEtaleModelTopology V)).obj (sfCbcModelRing V A) :=
  ((sheafificationAdjunction (proEtaleModelTopology T) CommRingCat.{u + 1}).homEquiv
    _ _).symm (Functor.whiskerLeft (proEtaleModelBaseChange f).op
      (toSheafify (proEtaleModelTopology V)
        ((Functor.const (proEtaleSiteModel V)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))

private def modelModuleDirect {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] :
    ConstantCompletion.Mod (sfCbcModelRing V A) ⥤
      ConstantCompletion.Mod (sfCbcModelRing T A) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleModelBaseChange f)
    (J := proEtaleModelTopology T) (K := proEtaleModelTopology V)
    (R := (sheafCompose (proEtaleModelTopology V)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sfCbcModelRing V A))
    (S := (sheafCompose (proEtaleModelTopology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sfCbcModelRing T A))
    ((sheafCompose (proEtaleModelTopology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (modelConstantMap f A))

private def modelModuleAdjunction {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] :
    (sfCbcMorphism f).modulePull (ULift.{u + 1} A) ⊣ modelModuleDirect f A := by
  let F := (sfCbcMorphism f).algebra
  let I := F.algebra (sfCbcModelRing T A)
  let c := ConstantCompletion.constantMap F (ULift.{u + 1} A)
  let g := SheafOfModules.RingedPresentationOnSites.siteContinuousRingedTopos
    (proEtaleModelBaseChange f) (sfCbcModelInverse f) (sfCbcModelAdjunction f)
    (sfCbcModelRing V A) (sfCbcModelRing T A) (modelConstantMap f A)
  have hc : (sheafCompose (proEtaleModelTopology V)
      (CategoryTheory.forget CommRingCat.{u + 1})).map c = I.ringUnderlying.inv ≫ g.ringMap := by
    have h := ConstantCompletion.constantInverseImageScalarNormalization
      (proEtaleModelTopology T) (proEtaleModelTopology V)
      (proEtaleModelBaseChange f) (sfCbcModelInverse f) (sfCbcModelAdjunction f)
      F (ULift.{u + 1} A)
    change I.ringUnderlying.hom ≫ _ = g.ringMap at h
    rw [← h, Iso.inv_hom_id_assoc]
  let a := Classical.choice
    (SheafOfModules.RingedPresentationOnSites.supplied_adjunction g
      (F.rings.obj (sfCbcModelRing T A)) I c hc)
  let e : ConstantCompletion.change c ≅
      SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u + 1} c :=
    NatIso.ofComponents (fun M ↦ eqToIso (by rfl)) (by
      intro M N a
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id, Category.id_comp]
      rfl)
  exact a.ofNatIsoLeft (isoWhiskerLeft I.modules e).symm

private def modelTransportIso (T : Scheme.{u}) (A : Type u) [CommRing A] :
    sfCbcModelModules T A ≅ SheafOfModules.pushforward.{u + 1}
      ((sheafCompose (proEtaleModelTopology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (sfCbcModelRingMap T A)) := by
  exact Functor.fullyFaithfulCancelRight (SheafOfModules.forget _) (eqToIso (by rfl))

private theorem modelConstantMap_square {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] :
    modelConstantMap f A ≫
        ((proEtaleModelBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (proEtaleModelTopology T) (proEtaleModelTopology V)).map
            (sfCbcModelRingMap V A) =
      sfCbcModelRingMap T A ≫
        ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
          CommRingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).map
            (proEtaleCoefficientDirectImageMap f A) := by
  apply ((sheafificationAdjunction (proEtaleModelTopology T)
    CommRingCat.{u + 1}).homEquiv _ _).injective
  apply NatTrans.ext
  funext Z
  have hm := congrArg (fun a ↦ a.app Z)
    (((sheafificationAdjunction (proEtaleModelTopology T) CommRingCat.{u + 1}).homEquiv
      ((Functor.const (proEtaleSiteModel T)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
      (((proEtaleModelBaseChange f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (proEtaleModelTopology T) (proEtaleModelTopology V)).obj
          (sfCbcModelRing V A))).apply_symm_apply
            (Functor.whiskerLeft (proEtaleModelBaseChange f).op
        (toSheafify (proEtaleModelTopology V)
          ((Functor.const (proEtaleSiteModel V)ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A))))))
  have ho := congrArg (fun a ↦ a.app (op (AsSmall.down.obj Z.unop)))
    (((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (adicConstantRing V A))).apply_symm_apply
          (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology V)
          ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))))
  change _ ≫ ((modelConstantMap f A).hom.app Z ≫ _) =
    _ ≫ ((sfCbcModelRingMap T A).hom.app Z ≫ _)
  rw [← Category.assoc, ← Category.assoc]
  change _ ≫ (modelConstantMap f A).hom.app Z = _ at hm
  rw [hm]
  let ZV := (proEtaleModelBaseChange f).obj Z.unop
  have hV := (sfCbcModelRingMap_existsUnique V A).exists.choose_spec.2 ZV
  have hT := (sfCbcModelRingMap_existsUnique T A).exists.choose_spec.2 Z.unop
  change (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        (op (AsSmall.down.obj Z.unop)) ≫
          (proEtaleCoefficientDirectImageMap f A).hom.app
            (op (AsSmall.down.obj Z.unop)) = _ at ho
  change (toSheafify (proEtaleModelTopology V)
      ((Functor.const (proEtaleSiteModel V)ᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app (op ZV) ≫
          (sfCbcModelRingMap V A).hom.app (op ZV) =
    ((toSheafify (proEtaleModelTopology T)
      ((Functor.const (proEtaleSiteModel T)ᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app Z ≫
          (sfCbcModelRingMap T A).hom.app Z) ≫
            (proEtaleCoefficientDirectImageMap f A).hom.app
              (op (AsSmall.down.obj Z.unop))
  exact hV.trans ((congrArg (fun k ↦ k ≫
    (proEtaleCoefficientDirectImageMap f A).hom.app
      (op (AsSmall.down.obj Z.unop))) hT).trans ho).symm

private def modelDirectSquare {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] :
    sfCbcModelModules V A ⋙ modelModuleDirect f A ≅
      proEtaleConstantModuleDirectImage f A ⋙ sfCbcModelModules T A := by
  let RT := adicModuleRing T A
  let RV := adicModuleRing V A
  let MT := (sheafCompose (proEtaleModelTopology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sfCbcModelRing T A)
  let MV := (sheafCompose (proEtaleModelTopology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (sfCbcModelRing V A)
  let dT : proEtaleSiteModel T ⥤ T.ProEt := AsSmall.down
  let dV : proEtaleSiteModel V ⥤ V.ProEt := AsSmall.down
  let cT : MT ⟶ (dT.sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology T) (ProEt.topology T)).obj RT :=
    (sheafCompose (proEtaleModelTopology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (sfCbcModelRingMap T A)
  let cV : MV ⟶ (dV.sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology V) (ProEt.topology V)).obj RV :=
    (sheafCompose (proEtaleModelTopology V)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (sfCbcModelRingMap V A)
  let rho : RT ⟶ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology T) (ProEt.topology V)).obj RV :=
    (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleCoefficientDirectImageMap f A)
  let rhom : MT ⟶ ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology T) (proEtaleModelTopology V)).obj MV :=
    (sheafCompose (proEtaleModelTopology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (modelConstantMap f A)
  have h : rhom ≫ ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology T) (proEtaleModelTopology V)).map cV =
    cT ≫ (dT.sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology T) (ProEt.topology T)).map rho := by
    exact (sheafCompose (proEtaleModelTopology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).congr_map (modelConstantMap_square f A)
  let eV := isoWhiskerRight (modelTransportIso V A) (modelModuleDirect f A)
  let e₁ := SheafOfModules.pushforwardComp.{u + 1}
    (F := proEtaleModelBaseChange f) (G := dV)
    (J := proEtaleModelTopology T) (K := proEtaleModelTopology V)
    (K' := ProEt.topology V) rhom cV
  let _ := Functor.isContinuous_comp (proEtaleModelBaseChange f) dV
    (proEtaleModelTopology T) (proEtaleModelTopology V) (ProEt.topology V)
  let e₂ := SheafOfModules.pushforwardCongr.{u + 1}
    (F := proEtaleModelBaseChange f ⋙ dV) (J := proEtaleModelTopology T)
    (K := ProEt.topology V) (S := MT) (R := RV) h
  let e₃ := SheafOfModules.pushforwardComp.{u + 1}
    (F := dT) (G := proEtaleBaseChange f)
    (J := proEtaleModelTopology T) (K := ProEt.topology T)
    (K' := ProEt.topology V) cT rho
  exact eV ≪≫ e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫
    isoWhiskerLeft (proEtaleConstantModuleDirectImage f A) (modelTransportIso T A).symm

private def modelPullComparison {V T : Scheme.{u}} (f : V ⟶ T)
    (A : Type u) [CommRing A] :
    sfCbcModelModules T A ⋙ (sfCbcMorphism f).modulePull (ULift.{u + 1} A) ⋙
        (sfCbcModelModules V A).asEquivalence.inverse ≅
      (proEtaleConstantModuleDirectImage f A).leftAdjoint := by
  let ET := (sfCbcModelModules T A).asEquivalence
  let EV := (sfCbcModelModules V A).asEquivalence
  let a := (ET.toAdjunction.comp (modelModuleAdjunction f A)).comp EV.symm.toAdjunction
  let er : EV.functor ⋙ (modelModuleDirect f A ⋙ ET.inverse) ≅
      proEtaleConstantModuleDirectImage f A :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (modelDirectSquare f A) ET.inverse ≪≫
        Functor.associator _ _ _ ≪≫
          isoWhiskerLeft (proEtaleConstantModuleDirectImage f A) ET.unitIso.symm ≪≫
            Functor.rightUnitor _
  exact (Functor.associator _ _ _).symm ≪≫
    (a.ofNatIsoRight er).leftAdjointUniq
      (Adjunction.ofIsRightAdjoint (proEtaleConstantModuleDirectImage f A))

private instance openSliceContinuous {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] :
    (cbcSliceFunctor T (cbcOpenObject j inferInstance)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject j inferInstance)) (ProEt.topology V) :=
  cbcSliceFunctor_continuous T (cbcOpenObject j inferInstance)

private instance openSliceCompContinuous {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] :
    (cbcSliceFunctor T (cbcOpenObject j inferInstance) ⋙ openMap j).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject j inferInstance)) (ProEt.topology T) :=
by
  let _ := openSliceContinuous j
  let _ := openMapContinuous j
  exact Functor.isContinuous_comp (cbcSliceFunctor T (cbcOpenObject j inferInstance))
    (openMap j) ((ProEt.topology T).over (cbcOpenObject j inferInstance))
      (ProEt.topology V) (ProEt.topology T)

private theorem openTranspose_unit {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] (A : Type u) [CommRing A] (Z : V.ProEt) :
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        (op ((openMap j).obj Z)) ≫
          (openConstantTranspose j (CommRingCat.of (ULift.{u + 1} A))).hom.app (op Z) =
    (toSheafify (ProEt.topology V)
      ((Functor.const V.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app (op Z) := by
  let B := CommRingCat.of (ULift.{u + 1} A)
  let P := (Functor.const T.ProEtᵒᵖ).obj B
  let Q := (Functor.const V.ProEtᵒᵖ).obj B
  have h := congrArg (fun f ↦ f.app (op ((openMap j).obj Z)))
    (((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv P
      ((proEtaleSheafDirectImage j CommRingCat.{u + 1}).obj
        (adicConstantRing V A))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange j).op (toSheafify (ProEt.topology V) Q)))
  change (toSheafify (ProEt.topology T) P).app (op ((openMap j).obj Z)) ≫
    (proEtaleCoefficientDirectImageMap j A).hom.app (op ((openMap j).obj Z)) = _ at h
  change (toSheafify (ProEt.topology T) P).app (op ((openMap j).obj Z)) ≫
    ((proEtaleCoefficientDirectImageMap j A).hom.app (op ((openMap j).obj Z)) ≫
      (adicConstantRing V A).obj.map ((openAdj j).unit.app Z).op) = _
  rw [← Category.assoc, h]
  exact ((toSheafify (ProEt.topology V) Q).naturality
    ((openAdj j).unit.app Z).op).symm.trans (Category.id_comp _)

private def openSliceForgetIso {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] :
    Over.forget (cbcOpenObject j inferInstance) ≅
      cbcSliceFunctor T (cbcOpenObject j inferInstance) ⋙ openMap j :=
  NatIso.ofComponents (fun Z ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 Z.left.left ≫ (Z.hom.left ≫ j) = Z.left.hom
      exact (Category.id_comp _).trans (MorphismProperty.Over.w Z.hom)))
    (by
      intro Z Z' f
      apply MorphismProperty.Over.Hom.ext
      change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
      simp)

private theorem openSliceCoefficient {V T : Scheme.{u}} (j : V ⟶ T)
    [IsOpenImmersion j] (A : Type u) [CommRing A] :
    let W := cbcOpenObject j inferInstance
    let c := openConstantTranspose j (CommRingCat.of (ULift.{u + 1} A))
    (Functor.sheafPushforwardContinuousNatTrans (openSliceForgetIso j).inv
        CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology T)).app
          (adicConstantRing T A) ≫
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology V)).map c =
      sfCbcConstantSliceMap T W A := by
  dsimp only
  let W := cbcOpenObject j inferInstance
  let c := openConstantTranspose j (CommRingCat.of (ULift.{u + 1} A))
  apply (sfCbcConstantSliceMap_existsUnique T W A).unique
  · intro Z
    let P := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))
    let η := toSheafify (ProEt.topology T) P
    change η.app (op Z.left) ≫
      ((adicConstantRing T A).obj.map ((openSliceForgetIso j).inv.app Z).op ≫
        c.hom.app (op ((cbcSliceFunctor T W).obj Z))) = _
    have hn := η.naturality ((openSliceForgetIso j).inv.app Z).op
    have hh : η.app (op Z.left) ≫
        (adicConstantRing T A).obj.map ((openSliceForgetIso j).inv.app Z).op =
      η.app (op ((openMap j).obj ((cbcSliceFunctor T W).obj Z))) :=
      hn.symm.trans (Category.id_comp _)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ c.hom.app (op ((cbcSliceFunctor T W).obj Z))) hh).trans
        (openTranspose_unit j A ((cbcSliceFunctor T W).obj Z)))
  · exact (sfCbcConstantSliceMap_existsUnique T W A).exists.choose_spec

end AlgebraicGeometry.Scheme
