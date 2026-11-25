/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction

/-! # Underlying abelian sheaf of ringed pro-etale pullback

## References

* Tags 03D2 and 03D3
-/

@[expose] public section
set_option autoImplicit false
universe t u v w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem smallUnderlying
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U]
    [Limits.PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback U (Type u) J K)]
    (L : Sheaf J RingCat.{u} ⥤ Sheaf K RingCat.{u})
    (aL : L ⊣ U.sheafPushforwardContinuous RingCat.{u} J K)
    (B : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    (aB : B ⊣ U.sheafPushforwardContinuous AddCommGrpCat.{u} J K)
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    (c : R ⟶ (U.sheafPushforwardContinuous RingCat.{u} J K).obj S)
    [IsIso ((aL.homEquiv R S).symm c)]
    (P : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    (aP : P ⊣ SheafOfModules.pushforward.{u} c) :
    Nonempty (P ⋙ SheafOfModules.toSheaf S ≅ SheafOfModules.toSheaf R ⋙ B) := by
  let G := U.sheafPushforwardContinuous RingCat.{u} J K
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U RingCat.{u} J K
  let e := aL.leftAdjointUniq b
  let z := asIso ((aL.homEquiv R S).symm c)
  let k := z.symm ≪≫ e.app R
  have hz : aL.unit.app R ≫ G.map z.hom = c :=
    (aL.homEquiv R S).apply_symm_apply c
  have hk : c ≫ G.map k.hom = b.unit.app R := by
    calc
      _ = aL.unit.app R ≫ G.map (z.hom ≫ z.inv ≫ e.hom.app R) := by
        rw [← hz]
        simp only [k, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
        rfl
      _ = aL.unit.app R ≫ G.map (e.hom.app R) := by rw [Iso.hom_inv_id_assoc]
      _ = _ := Adjunction.unit_leftAdjointUniq_hom_app aL b R
  let V := CategoryTheory.forget RingCat.{u}
  let q := CategoryTheory.sheafPullbackForgetIso J K U V
  let pr : SheafPullbackUnitPresentation (F := U)
      ((sheafCompose J V).obj R) ((sheafCompose K V).obj S) :=
    { unit := (sheafCompose J V).map c
      iso := (sheafCompose K V).mapIso k ≪≫ q.app R
      equation := by
        intro W x
        have h : (sheafCompose J V).map c ≫
            (U.sheafPushforwardContinuous (Type u) J K).map
              (((sheafCompose K V).mapIso k ≪≫ q.app R).hom) =
            (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              U (Type u) J K).unit.app ((sheafCompose J V).obj R) := by
          change (sheafCompose J V).map c ≫
            ((U.sheafPushforwardContinuous (Type u) J K).map
              ((sheafCompose K V).map k.hom) ≫
              (U.sheafPushforwardContinuous (Type u) J K).map (q.hom.app R)) = _
          rw [← Category.assoc]
          change (sheafCompose J V).map (c ≫ G.map k.hom) ≫ _ = _
          rw [hk]
          exact CategoryTheory.sheafPullbackForgetIso_unit J K U V R
        exact congrArg (fun f ↦ f.hom.app W x) h }
  obtain ⟨h, _⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation c pr rfl
  let p := aP.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction c)
  let ab := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U AddCommGrpCat.{u} J K).leftAdjointUniq aB
  exact ⟨Functor.isoWhiskerRight p (SheafOfModules.toSheaf S) ≪≫ h ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R) ab⟩

private noncomputable def modelEquivalence (Z : Scheme.{t})
    (D : Type v) [Category.{w} D] :
    Sheaf (coefficientProEtaleModelTopology.{t, u} Z) D ≌ Sheaf (ProEt.topology Z) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : Z.ProEt ⥤ coefficientProEtaleSiteModel.{t, u} Z).sheafPushforwardContinuous
      D (ProEt.topology Z) (coefficientProEtaleModelTopology Z))
    ((AsSmall.down : coefficientProEtaleSiteModel.{t, u} Z ⥤ Z.ProEt).sheafPushforwardContinuous
      D (coefficientProEtaleModelTopology Z) (ProEt.topology Z))
    (Iso.refl _) (Iso.refl _)

private noncomputable def modelModuleEquivalence (Z : Scheme.{t})
    (R : Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)}) :
    SheafOfModules.{max u (t + 1)}
        ((modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}).inverse.obj R) ≌
      SheafOfModules.{max u (t + 1)} R := by
  let : (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Z.ProEt)).functor.IsContinuous
      (ProEt.topology Z) (coefficientProEtaleModelTopology.{t, u} Z) :=
    coefficientProEtaleModelUp_isContinuous Z
  let : (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Z.ProEt)).inverse.IsContinuous
      (coefficientProEtaleModelTopology.{t, u} Z) (ProEt.topology Z) := by
    change (AsSmall.down : coefficientProEtaleSiteModel.{t, u} Z ⥤ Z.ProEt).IsContinuous
      (coefficientProEtaleModelTopology.{t, u} Z) (ProEt.topology Z)
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence.{max u (t + 1)}
    (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Z.ProEt))
    (S := R)
    (R := (modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}).inverse.obj R)
    (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.obj.map_id _)
    (by ext : 2; exact R.obj.map_id _)

private noncomputable def modelForgetIso (Z : Scheme.{t})
    (R : Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)}) :
    (modelModuleEquivalence Z R).inverse ⋙
        SheafOfModules.toSheaf
          ((modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}).inverse.obj R) ≅
      SheafOfModules.toSheaf R ⋙
        (modelEquivalence.{t, u} Z AddCommGrpCat.{max u (t + 1)}).inverse :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

private noncomputable def modelForgetForwardIso (Z : Scheme.{t})
    (R : Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)}) :
    (modelModuleEquivalence Z R).functor ⋙ SheafOfModules.toSheaf R ≅
      SheafOfModules.toSheaf
          ((modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}).inverse.obj R) ⋙
        (modelEquivalence.{t, u} Z AddCommGrpCat.{max u (t + 1)}).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Pullback with an invertible coefficient adjunct has ordinary abelian inverse
image as its underlying sheaf. The coefficient rings and the adjoints are arbitrary. -/
theorem proEtale_ringedPullback_underlying_of_isIso
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (L : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    (aL : L ⊣ (proEtaleBaseChange f).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X))
    (B : Sheaf (ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)})
    (aB : B ⊣ (proEtaleBaseChange f).sheafPushforwardContinuous
      AddCommGrpCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X))
    (R : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)})
    (S : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    (c : R ⟶ ((proEtaleBaseChange f).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).obj S)
    [IsIso ((aL.homEquiv R S).symm c)]
    (P : SheafOfModules.{max u (t + 1)} R ⥤ SheafOfModules.{max u (t + 1)} S)
    (aP : P ⊣ SheafOfModules.pushforward.{max u (t + 1)} c) :
    Nonempty (P ⋙ SheafOfModules.toSheaf S ≅ SheafOfModules.toSheaf R ⋙ B) := by
  let eRY := modelEquivalence.{t, u} Y RingCat.{max u (t + 1)}
  let eRX := modelEquivalence.{t, u} X RingCat.{max u (t + 1)}
  let eAY := modelEquivalence.{t, u} Y AddCommGrpCat.{max u (t + 1)}
  let eAX := modelEquivalence.{t, u} X AddCommGrpCat.{max u (t + 1)}
  let eY := modelModuleEquivalence Y R
  let eX := modelModuleEquivalence X S
  let R' := eRY.inverse.obj R
  let S' := eRX.inverse.obj S
  let U := coefficientProEtaleModelBaseChange.{t, u} f
  let J := coefficientProEtaleModelTopology.{t, u} Y
  let K := coefficientProEtaleModelTopology.{t, u} X
  let c' : R' ⟶ (U.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).obj S' :=
    ⟨Functor.whiskerLeft AsSmall.down.op c.hom⟩
  let L' := eRY.functor ⋙ L ⋙ eRX.inverse
  let B' := eAY.functor ⋙ B ⋙ eAX.inverse
  let aL' : L' ⊣ U.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K :=
    aL.restrictFullyFaithful eRY.fullyFaithfulFunctor eRX.fullyFaithfulFunctor
      (Iso.refl _) (Iso.refl _)
  let aB' : B' ⊣ U.sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)} J K :=
    aB.restrictFullyFaithful eAY.fullyFaithfulFunctor eAX.fullyFaithfulFunctor
      (Iso.refl _) (Iso.refl _)
  let P' := SheafOfModules.pullback.{max u (t + 1)} c'
  let aP' := SheafOfModules.pullbackPushforwardAdjunction.{max u (t + 1)} c'
  let ePush : eX.inverse ⋙ SheafOfModules.pushforward.{max u (t + 1)} c' ⋙
      eY.functor ≅ SheafOfModules.pushforward.{max u (t + 1)} c :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
        intro W V g
        ext x
        rfl))) (by
      intro M N g
      ext W x
      rfl)
  let aT := ((eY.symm.toAdjunction.comp aP').comp eX.toAdjunction).ofNatIsoRight ePush
  let eP := aP.leftAdjointUniq aT
  have hu : aL'.unit.app R' =
      ⟨Functor.whiskerLeft AsSmall.down.op (aL.unit.app R).hom⟩ := by
    apply eRY.functor.map_injective
    dsimp only [aL']
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Iso.refl_hom, NatTrans.id_app]
    rfl
  have hm : (aL'.homEquiv R' S').symm c' =
      eRX.inverse.map ((aL.homEquiv R S).symm c) := by
    apply (aL'.homEquiv R' S').injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, hu]
    change eRY.inverse.map c =
      eRY.inverse.map (aL.unit.app R ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous
          RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).map
            ((aL.homEquiv R S).symm c))
    exact congrArg eRY.inverse.map ((aL.homEquiv R S).apply_symm_apply c).symm
  have : IsIso ((aL'.homEquiv R' S').symm c') := by rw [hm]; infer_instance
  let : (AsSmall.down :
      coefficientProEtaleSiteModel.{t, u} Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs
      (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up :
      X.ProEt ⥤ coefficientProEtaleSiteModel.{t, u} X).IsEquivalence :=
    inferInstanceAs
      (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).functor.IsEquivalence
  have : Limits.PreservesFiniteLimits U := by
    dsimp [U, coefficientProEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  obtain ⟨h⟩ := smallUnderlying J K U L' aL' B' aB' R' S' c' P' aP'
  let V := SheafOfModules.toSheaf.{max u (t + 1)} R
  let W := SheafOfModules.toSheaf.{max u (t + 1)} S
  let s₁ := Functor.isoWhiskerRight eP W
  let s₂ := Functor.isoWhiskerLeft (eY.inverse ⋙ P') (modelForgetForwardIso X S)
  let s₃ := Functor.isoWhiskerLeft eY.inverse (Functor.isoWhiskerRight h eAX.functor)
  let s₄ := Functor.isoWhiskerRight (modelForgetIso Y R)
    (eAY.functor ⋙ B ⋙ eAX.inverse ⋙ eAX.functor)
  let s₅ := Functor.isoWhiskerLeft V
    (Functor.isoWhiskerRight eAY.counitIso (B ⋙ eAX.inverse ⋙ eAX.functor) ≪≫
      (B ⋙ eAX.inverse ⋙ eAX.functor).leftUnitor)
  let s₆ := Functor.isoWhiskerLeft (V ⋙ B) eAX.counitIso ≪≫ (V ⋙ B).rightUnitor
  exact ⟨s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅ ≪≫ s₆⟩

end AlgebraicGeometry.Scheme
