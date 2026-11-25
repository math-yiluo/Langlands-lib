/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization

import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Transport of a single local model across open extension by zero

Source: Bhatt--Scholze, Lemma 6.1.12(1) and Proposition 6.6.11
(blueprint: lem-cbc-extension-zero-perfect-model-transport).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private def constantPF (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantPresheafHomEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) (M : ModuleCat.{u + 1} A)
    (F : _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))) :
    ((constantPF X A).obj M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl

private def constantPFAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    constantPF X A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv X A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

private def constantGlobal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) :=
  SheafOfModules.forget (adicLisseRing X A) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit X A) ⋙
      PresheafOfModules.evaluation _ (op T)

private def constantAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantModules X A ⊣ constantGlobal X A T :=
  (constantPFAdj X A T hT).comp
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit X A))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private def integralGlobal {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) :=
  pbcRestrict (exchangeScalar d X) ⋙ constantGlobal X A T

private def integralAdj {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) (hT : IsTerminal T) :
    integralConstantModule X d ⊣ integralGlobal X d T := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcCompletedComparison X d).symm)
  let adj := ((constantAdj X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X pd))).comp e.toAdjunction
  exact adj

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem integralScalarDirect {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    exchangeScalar d Y ≫ proEtaleRingDirectImageMap f
        (d.completedRing Y) (d.completedRing X) (d.integralRingIso f) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (exchangeScalar d X) := by
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have h := congrArg (fun z ↦ (adj.homEquiv _ _) z) (exchangeScalar_comm d f)
  rw [adj.homEquiv_naturality_left] at h
  rw [adj.homEquiv_naturality_right] at h
  change _ = _ at h
  have hc : (adj.homEquiv _ _) (exchangeConstantIso f A).hom =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hc] at h
  exact h.symm

private theorem integralScalarSections {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app V ≫
        (exchangeScalar d Y).hom.app V ≫
        (proEtaleRingDirectImageMap f (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso f)).hom.app V =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
          ((proEtaleBaseChange f).op.obj V) ≫
            (exchangeScalar d X).hom.app ((proEtaleBaseChange f).op.obj V) := by
  have h := congrArg (fun z ↦ z.hom.app V) (integralScalarDirect d f)
  have hc := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of A)))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  have hcV := congrArg (fun z ↦ z.app V) hc
  change (toSheafify _ _).app V ≫
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom.app V =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
          ((proEtaleBaseChange f).op.obj V) at hcV
  change (exchangeScalar d Y).hom.app V ≫
      (proEtaleRingDirectImageMap f (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso f)).hom.app V =
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A)).hom.app V ≫
      (exchangeScalar d X).hom.app ((proEtaleBaseChange f).op.obj V) at h
  rw [h, ← Category.assoc, hcV]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private def integralGlobalDirectIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Y.ProEt) :
    proEtaleRingModuleDirectImage f (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso f) ⋙ integralGlobal Y d T ≅
      integralGlobal X d ((proEtaleBaseChange f).obj T) :=
  NatIso.ofComponents (fun N ↦ by
    let e : (integralGlobal Y d T).obj
        ((proEtaleRingModuleDirectImage f (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso f)).obj N) ≃ₗ[A]
        (integralGlobal X d ((proEtaleBaseChange f).obj T)).obj N :=
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a n
          have h := congrArg
            (fun z ↦ ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map z).hom a)
            (integralScalarSections d f (op T))
          let n' : N.val.obj (op ((proEtaleBaseChange f).obj T)) := n
          change
            ((proEtaleRingDirectImageMap f (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso f)).hom.app (op T))
                ((exchangeScalar d Y).hom.app (op T)
                  ((toSheafify (ProEt.topology Y)
                    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))).app (op T) a)) • n' =
            (exchangeScalar d X).hom.app ((proEtaleBaseChange f).op.obj (op T))
              ((toSheafify (ProEt.topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
                  ((proEtaleBaseChange f).op.obj (op T)) a) • n'
          exact congrArg (fun c : (d.completedRing X).obj.obj
            (op ((proEtaleBaseChange f).obj T)) ↦ c • n') h }
    exact e.toModuleIso)
    (by intros; ext x; rfl)

private def integralConstantPullIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralConstantModule Y d ⋙
        proEtaleRingModulePullback f (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso f) ≅ integralConstantModule X d := by
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let adj := ((integralAdj Y d T hT).comp
    (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso f))).ofNatIsoRight (integralGlobalDirectIso d f T)
  exact adj.leftAdjointUniq (integralAdj X d ((proEtaleBaseChange f).obj T)
    (hT.isTerminalObj (proEtaleBaseChange f)))

private def integralConstantDerivedPullIso {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralConstantDerived Y d ⋙ d.pull f ≅ integralConstantDerived X d := by
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  let : (integralConstantModule X d).Additive := integralConstantModule_additive X d
  let : (integralConstantModule Y d).Additive := integralConstantModule_additive Y d
  let := (integralConstantModule_exact Y d).1
  let := (integralConstantModule_exact Y d).2
  let := (integralConstantModule_exact X d).1
  let := (integralConstantModule_exact X d).2
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (integralConstantPullIso d f)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

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

private def rawPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage f R := by
  let e := pullbackScalarIso f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _)
  exact e

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private def sliceDerivedIso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (V : X.ProEt)
    (K : DerivedCategory (pbcModules X R)) :
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      R V).mapDerivedCategory.obj K ≅
      ringedSiteDerivedRestrictionOfUniverses.{u + 1, u, u + 1, u + 1, u + 2, u + 2}
        ((adicLisseForget X).obj R) V K :=
  ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
    R V).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      R V).mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

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

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

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

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

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

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
