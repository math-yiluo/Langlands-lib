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

/-! # Module units from abelian units in independent universes

## References

* Stacks Project, Modules on Sites, Tags 03D2 and 03D3
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private abbrev ringPush {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology Y) (ProEt.topology X)

private theorem smallUnitBijective
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
    (aP : P ⊣ SheafOfModules.pushforward.{u} c)
    (W₀ : Cᵒᵖ) (M : SheafOfModules.{u} R)
    (hb : Function.Bijective ((aB.unit.app ((SheafOfModules.toSheaf R).obj M)).hom.app W₀)) :
    Function.Bijective ((aP.unit.app M).val.app W₀) := by
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
  obtain ⟨h, hh⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation c pr rfl
  let E := sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj W₀
  let bA := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U AddCommGrpCat.{u} J K
  have : IsIso (E.map (aB.unit.app ((SheafOfModules.toSheaf R).obj M))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hbA := congrArg E.map
    (Adjunction.unit_leftAdjointUniq_hom_app aB bA ((SheafOfModules.toSheaf R).obj M))
  rw [E.map_comp] at hbA
  have : IsIso (E.map (bA.unit.app ((SheafOfModules.toSheaf R).obj M))) := by
    rw [← hbA]
    infer_instance
  have he := congrArg E.map (hh M)
  rw [E.map_comp] at he
  have : IsIso (E.map ((SheafOfModules.toSheaf R).map
      ((SheafOfModules.pullbackPushforwardAdjunction c).unit.app M))) := by
    have : IsIso (E.map ((SheafOfModules.toSheaf R).map
        ((SheafOfModules.pullbackPushforwardAdjunction c).unit.app M)) ≫
          E.map ((U.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (h.hom.app M))) :=
      he ▸ inferInstance
    exact IsIso.of_isIso_comp_right _
      (E.map ((U.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (h.hom.app M)))
  let EM := SheafOfModules.evaluation R W₀
  have : IsIso (EM.map ((SheafOfModules.pullbackPushforwardAdjunction c).unit.app M)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConcreteCategory.bijective_of_isIso
        (E.map ((SheafOfModules.toSheaf R).map
          ((SheafOfModules.pullbackPushforwardAdjunction c).unit.app M))))
  have hp := congrArg EM.map (Adjunction.unit_leftAdjointUniq_hom_app aP
    (SheafOfModules.pullbackPushforwardAdjunction c) M)
  rw [EM.map_comp] at hp
  have : IsIso (EM.map (aP.unit.app M)) := by
    have : IsIso (EM.map (aP.unit.app M) ≫
        EM.map ((SheafOfModules.pushforward c).map
          ((aP.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction c)).hom.app M))) :=
      hp ▸ inferInstance
    exact IsIso.of_isIso_comp_right _
      (EM.map ((SheafOfModules.pushforward c).map
        ((aP.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction c)).hom.app M)))
  exact ConcreteCategory.bijective_of_isIso (EM.map (aP.unit.app M))

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

-- Comparing the module adjunctions expands the coefficient-sized site transports.
/-- An invertible inverse-image coefficient map transfers sectionwise bijectivity
of the actual abelian unit to the actual module unit, for independent universes. -/
theorem proEtale_module_unit_bijective_of_abelian
    {X Z : Scheme.{t}} (i : Z ⟶ X) (V : X.ProEt)
    (R : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)})
    (S : Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)})
    (c : R ⟶ ((proEtaleBaseChange i).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z)).obj S)
    (L : Sheaf (ProEt.topology X) RingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)})
    (aL : L ⊣ (proEtaleBaseChange i).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z))
    [IsIso ((aL.homEquiv R S).symm c)]
    (B : Sheaf (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology Z) AddCommGrpCat.{max u (t + 1)})
    (aB : B ⊣ (proEtaleBaseChange i).sheafPushforwardContinuous
      AddCommGrpCat.{max u (t + 1)} (ProEt.topology X) (ProEt.topology Z))
    (P : SheafOfModules.{max u (t + 1)} R ⥤ SheafOfModules.{max u (t + 1)} S)
    (aP : P ⊣ SheafOfModules.pushforward c)
    (M : SheafOfModules.{max u (t + 1)} R)
    (habelian : Function.Bijective
      ((aB.unit.app ((SheafOfModules.toSheaf R).obj M)).hom.app (op V))) :
    Function.Bijective ((aP.unit.app M).val.app (op V)) := by
  let eRX := modelEquivalence.{t, u} X RingCat.{max u (t + 1)}
  let eRZ := modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}
  let eAX := modelEquivalence.{t, u} X AddCommGrpCat.{max u (t + 1)}
  let eAZ := modelEquivalence.{t, u} Z AddCommGrpCat.{max u (t + 1)}
  let eX := modelModuleEquivalence X R
  let eZ := modelModuleEquivalence Z S
  let R' := eRX.inverse.obj R
  let S' := eRZ.inverse.obj S
  let U := coefficientProEtaleModelBaseChange.{t, u} i
  let J := coefficientProEtaleModelTopology.{t, u} X
  let K := coefficientProEtaleModelTopology.{t, u} Z
  let c' : R' ⟶ (U.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K).obj S' :=
    ⟨Functor.whiskerLeft AsSmall.down.op c.hom⟩
  let L' := eRX.functor ⋙ L ⋙ eRZ.inverse
  let B' := eAX.functor ⋙ B ⋙ eAZ.inverse
  let aL' : L' ⊣ U.sheafPushforwardContinuous RingCat.{max u (t + 1)} J K :=
    aL.restrictFullyFaithful eRX.fullyFaithfulFunctor eRZ.fullyFaithfulFunctor
      (Iso.refl _) (Iso.refl _)
  let aB' : B' ⊣ U.sheafPushforwardContinuous AddCommGrpCat.{max u (t + 1)} J K :=
    aB.restrictFullyFaithful eAX.fullyFaithfulFunctor eAZ.fullyFaithfulFunctor
      (Iso.refl _) (Iso.refl _)
  have hu : aL'.unit.app R' =
      ⟨Functor.whiskerLeft AsSmall.down.op (aL.unit.app R).hom⟩ := by
    apply eRX.functor.map_injective
    dsimp only [aL']
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Iso.refl_hom, NatTrans.id_app]
    rfl
  have hm : (aL'.homEquiv R' S').symm c' =
      eRZ.inverse.map ((aL.homEquiv R S).symm c) := by
    apply (aL'.homEquiv R' S').injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, hu]
    change eRX.inverse.map c = eRX.inverse.map
      (aL.unit.app R ≫ (ringPush.{t, u} i).map ((aL.homEquiv R S).symm c))
    exact congrArg eRX.inverse.map ((aL.homEquiv R S).apply_symm_apply c).symm
  have : IsIso ((aL'.homEquiv R' S').symm c') := by rw [hm]; infer_instance
  let : (AsSmall.down :
      coefficientProEtaleSiteModel.{t, u} X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs
      (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up :
      Z.ProEt ⥤ coefficientProEtaleSiteModel.{t, u} Z).IsEquivalence :=
    inferInstanceAs
      (AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Z.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits U := by
    dsimp [U, coefficientProEtaleModelBaseChange]
    infer_instance
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let am := SheafOfModules.pullbackPushforwardAdjunction c'
  let N := eX.inverse.obj M
  have hb : Function.Bijective
      ((aB'.unit.app ((SheafOfModules.toSheaf R').obj N)).hom.app
        (op (AsSmall.up.obj V))) := by
    have heq : aB'.unit.app ((SheafOfModules.toSheaf R').obj N) =
        ⟨Functor.whiskerLeft AsSmall.down.op
          (aB.unit.app ((SheafOfModules.toSheaf R).obj M)).hom⟩ := by
      apply eAX.functor.map_injective
      dsimp only [aB']
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      simp only [Iso.refl_hom, NatTrans.id_app]
      rfl
    rw [heq]
    exact habelian
  have hbmod := smallUnitBijective J K U L' aL' B' aB' R' S' c'
    (SheafOfModules.pullback c') am (op (AsSmall.up.obj V)) N hb
  let ePush : eZ.inverse ⋙ SheafOfModules.pushforward c' ⋙ eX.functor ≅
      SheafOfModules.pushforward c :=
    NatIso.ofComponents (fun T ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
        intro W W' g
        ext x
        rfl))) (by
      intro T T' g
      ext W x
      rfl)
  let adj := eX.symm.toAdjunction.comp (am.comp eZ.toAdjunction)
  let ac := adj.ofNatIsoRight ePush
  let EM := SheafOfModules.evaluation R (op V)
  have h₂ : IsIso (EM.map (eX.functor.map (am.unit.app N))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbmod
  have : IsIso (EM.map (adj.unit.app M)) := by
    have h₁ : IsIso (EM.map (eX.symm.toAdjunction.unit.app M)) := inferInstance
    have h₃ : IsIso (EM.map (eX.symm.inverse.map
        ((SheafOfModules.pushforward c').map
          (eZ.toAdjunction.unit.app ((SheafOfModules.pullback c').obj N))))) := inferInstance
    change IsIso (EM.map ((eX.symm.toAdjunction.comp (am.comp eZ.toAdjunction)).unit.app M))
    rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
    let f := eX.symm.toAdjunction.unit.app M
    let g := eX.symm.inverse.map (am.unit.app N)
    let h := eX.symm.inverse.map ((SheafOfModules.pushforward c').map
      (eZ.toAdjunction.unit.app ((SheafOfModules.pullback c').obj N)))
    have he : EM.map (f ≫ g ≫ h) = EM.map f ≫ EM.map g ≫ EM.map h :=
      (EM.map_comp f (g ≫ h)).trans (congrArg (fun q ↦ EM.map f ≫ q) (EM.map_comp g h))
    erw [eX.symm.inverse.map_comp]
    change IsIso (EM.map (f ≫ g ≫ h))
    rw [he]
    exact @IsIso.comp_isIso _ _ _ _ _ (EM.map f) (EM.map g ≫ EM.map h) h₁
      (@IsIso.comp_isIso _ _ _ _ _ (EM.map g) (EM.map h) h₂ h₃)
  have : IsIso (EM.map (ac.unit.app M)) := by
    change IsIso (EM.map (adj.unit.app M ≫ ePush.hom.app _))
    rw [EM.map_comp]
    infer_instance
  have he := congrArg EM.map
    (Adjunction.unit_leftAdjointUniq_hom_app ac aP M)
  rw [EM.map_comp] at he
  have : IsIso (EM.map (aP.unit.app M)) := by
    rw [← he]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (EM.map (aP.unit.app M))

end AlgebraicGeometry.Scheme
