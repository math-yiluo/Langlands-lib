/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
public import Mathlib.CategoryTheory.Adjunction.Whiskering

import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralCoefficientPullbackExistence
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLinePullbackLowerTensor
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorAdjointEvaluation
import Mathlib.CategoryTheory.HomCongr

/-! # Restriction of coefficients in the ordinary geometric adjunction

Source: blueprint classes proof (2); Stacks 03EL, ordinary coefficient extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Direct image of whole abelian towers, taken componentwise.
Source: classes (2), ordinary system topos
(blueprint: lem-sp-tower-restricted-scalar-adjunction). -/
abbrev abPush {X Y : Scheme.{u}} (f : X ⟶ Y) : Ab X ⥤ Ab Y :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb X) (DiagonalAb Y)).obj
    (lowerStar AddCommGrpCat.{u + 1} f)

/-- The componentwise ordinary abelian adjunction.
Source: classes (2), ordinary system topos
(blueprint: lem-sp-tower-restricted-scalar-adjunction). -/
def abAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) : abPull f ⊣ abPush f :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).whiskerRight ℕᵒᵖ

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.transition SemilinearSections.coefficientMap
  Scheme.proEtaleRingModulePullback Scheme.proEtaleRingModuleAdjunction
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
  PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars

attribute [local implicit_reducible] Scheme.ProEt spCoefficientCommRings SpTowerShriek.tau
  SemilinearSections.evaluation CategoryTheory.Functor.ofOpSequence
  CategoryTheory.Functor.ofSequence
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj Scheme.proEtaleRingModuleDirectImage

private theorem cancelMappedIso
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {P Q S : C} (e : P ≅ Q) {A B : D}
    (a : A ⟶ B) (b : B ⟶ R.obj P) (c : P ⟶ S) :
    (a ≫ b ≫ R.map e.hom) ≫ R.map (e.inv ≫ c) = a ≫ b ≫ R.map c := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    ← R.map_comp_assoc, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem adjointPost_apply (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    {N P : proEtaleRingModules X (proEtaleConstantRing X A)}
    (a : (proEtaleConstantRingPullback A f).obj M ⟶ N) (b : N ⟶ P)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((adj.homEquiv _ _) (a ≫ b)).val.app U x =
      b.val.app (chart f U) (((adj.homEquiv _ _) a).val.app U x) := by
  rw [adj.homEquiv_naturality_right, evaluated_comp_apply, pushforward_map_apply]

private theorem adjointPost_heq (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    {N P : proEtaleRingModules X (proEtaleConstantRing X A)}
    (a : (proEtaleConstantRingPullback A f).obj M ⟶ N) (b : N ⟶ P)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) (z : N.val.obj (chart f U))
    (hz : HEq (((adj.homEquiv _ _) a).val.app U x) z) :
    HEq (((adj.homEquiv _ _) (a ≫ b)).val.app U x) (b.val.app (chart f U) z) := by
  exact (heq_of_eq (adjointPost_apply A f adj a b U x)).trans
    (heq_of_eq (congr_heq (HEq.refl (fun w ↦ b.val.app (chart f U) w)) hz))

private theorem pushHorizontal_sections
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (N : Systems X (Arings l E X))
    {m n : ℕ} (h : n ≤ m) (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y m).obj (g.push.obj N)).val.obj U)
    (y : ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)).val.obj U)
    (hy : HEq
      (((SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h).app
          (g.push.obj N)).val.app U x) y)
    (z : ((SpTowerShriek.ev l E X m).obj N).val.obj (chart f U))
    (hz : HEq (((g.ordinaryPushEvaluation m).hom.app N).val.app U x) z) :
    HEq (((g.ordinaryPushEvaluation n).hom.app N).val.app U y)
      (((SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app N).val.app
          (chart f U) z) := by
  let M := g.push.obj N
  let ε : g.pull.obj M ⟶ N := g.ordinaryAdjunction.counit.app N
  let tP := (SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app (g.pull.obj M)
  let tN := (SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app N
  let φ := SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h
  let R := SemilinearSections.res.{u + 1, u, u + 1} φ
  let pm := (g.ordinaryPullEvaluation m).app M
  let pn := (g.ordinaryPullEvaluation n).app M
  let δ := pn.inv ≫ (SpTowerShriek.ev l E X n).map ε
  let k := pm.inv ≫ tP ≫ R.map pn.hom
  have hu := actual_unit_transition l E f g M h U x y hy
  have hp := lowerPath_section (SpTowerShriek.R l E m) (SpTowerShriek.R l E n) f
    (proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f)
    (proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f) φ
    (Iso.refl _) (Iso.refl _) k δ U x y hu
  have hn : tP ≫ R.map ((SpTowerShriek.ev l E X n).map ε) =
      (SpTowerShriek.ev l E X m).map ε ≫ tN :=
    ((SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).naturality ε).symm
  have hk : k ≫ R.map δ = (pm.inv ≫ (SpTowerShriek.ev l E X m).map ε) ≫ tN := by
    exact (cancelMappedIso R pn pm.inv tP ((SpTowerShriek.ev l E X n).map ε)).trans
      ((congrArg (fun t ↦ pm.inv ≫ t) hn).trans (Category.assoc _ _ _).symm)
  have he (j : ℕ) :
      ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E j) f).homEquiv _ _)
        ((g.ordinaryPullEvaluation j).inv.app M ≫
          (SpTowerShriek.ev l E X j).map ε) =
      (g.ordinaryPushEvaluation j).hom.app N := by
    have hh := TensorCoordinates.tensorComparison_adjoint_evaluation l E g ε j
    have hc : (g.ordinaryAdjunction.homEquiv _ N) ε = 𝟙 _ := by
      dsimp only [ε]
      rw [← g.ordinaryAdjunction.homEquiv_symm_id N]
      exact Equiv.apply_symm_apply _ _
    rw [hc, CategoryTheory.Functor.map_id, Category.id_comp] at hh
    exact hh.symm
  simp only [Iso.refl_hom, Iso.refl_inv, CategoryTheory.Functor.map_id,
    Category.id_comp] at hp
  change HEq
    ((((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _)
      (k ≫ R.map δ)).val.app U x)
    ((((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
      δ).val.app U y) at hp
  have hen : ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
      δ = (g.ordinaryPushEvaluation n).hom.app N := he n
  have hem : ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _)
      (pm.inv ≫ (SpTowerShriek.ev l E X m).map ε) =
      (g.ordinaryPushEvaluation m).hom.app N := he m
  have hm := congrArg (fun k ↦ k.val.app U x) hem
  have hb := adjointPost_heq (SpTowerShriek.R l E m) f
    (proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f)
    (pm.inv ≫ (SpTowerShriek.ev l E X m).map ε) tN U x z
      ((heq_of_eq hm).trans hz)
  have hl := congrArg (fun k ↦
    (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _)
      k).val.app U x) hk
  have hr := congrArg (fun k ↦ k.val.app U y) hen
  exact (heq_of_eq hr.symm).trans (hp.symm.trans ((heq_of_eq hl).trans hb))

private theorem transportPushSections
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (n : ℕ)
    (B' : ℕ → Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (τ' : ∀ k, B' (k + 1) ⟶ B' k)
    (hB : B' = SpTowerShriek.B l E X) (hτ : HEq τ' (SpTowerShriek.tau l E X))
    (G : SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) B' τ' ⥤ SpTowerShriek.S l E Y)
    (hG : HEq g.push G)
    (q : Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (B' n),
      Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B' n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P)
    (hq : HEq q
      (⟨proEtaleConstantRingPullback (SpTowerShriek.R l E n) f,
        proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f,
        proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n),
          Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n) ⥤
            SemilinearSections.Mod.{u + 1, u, u + 1}
              (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n), L ⊣ P))
    (e : G ⋙ SpTowerShriek.ev l E Y n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) B' τ' n ⋙ q.2.1)
    (he : HEq (g.ordinaryPushEvaluation n) e)
    (hs : ∀ N U (x : ((SpTowerShriek.ev l E Y n).obj (G.obj N)).val.obj U),
      HEq ((e.hom.app N).val.app U x) x) :
    ∀ N U (x : ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)).val.obj U),
      HEq (((g.ordinaryPushEvaluation n).hom.app N).val.app U x) x := by
  subst B'
  cases eq_of_heq hτ
  cases eq_of_heq hG
  cases eq_of_heq hq
  cases eq_of_heq he
  exact hs

private theorem pushEvaluationSections
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (n : ℕ)
    (N : Systems X (Arings l E X)) (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)).val.obj U) :
    HEq (((g.ordinaryPushEvaluation n).hom.app N).val.app U x) x := by
  exact transportPushSections l E g n
    g.generic.coefficients g.generic.coefficientTransition g.coefficients g.transitions
    g.generic.push g.push_eq
    ⟨(g.generic.inverseImage n).modules, g.generic.levelPush n, g.generic.levelAdjunction n⟩
    (g.levelAdjunction_eq n) (g.generic.ordinaryPushEvaluation n)
    (g.ordinaryPushEvaluation_eq n) (g.generic.ordinaryPushEvaluation_sections n) N U x

private abbrev integralEvaluation (T : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op) n

private abbrev levelAb (T : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.toSheaf.{u + 1}
    (SemilinearSections.ring.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))

private def restrictionEvaluationAb (T : Scheme.{u})
    (M : Systems T (Arings l E T)) (n : ℕ) :
    (SheafOfModules.toSheaf _).obj
      ((integralEvaluation l T n).obj
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E T)).obj M)) ≅
      (levelAb l E T n).obj ((SpTowerShriek.ev l E T n).obj M) :=
  Iso.refl _

private def restrictedPushLevel
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (N : Systems X (Arings l E X)) (n : ℕ) :
    (FY.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n) ≅
    (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((FX.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E X)).obj N)).obj (op n)) :=
  forgetEvaluationIso Y (Rrings l Y) FY _ n ≪≫
    restrictionEvaluationAb l E Y _ n ≪≫
    (levelAb l E Y n).mapIso ((g.ordinaryPushEvaluation n).app N) ≪≫
    (show (levelAb l E Y n).obj
        ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj
          ((SpTowerShriek.ev l E X n).obj N)) ≅
      (lowerStar AddCommGrpCat.{u + 1} f).obj
        ((levelAb l E X n).obj ((SpTowerShriek.ev l E X n).obj N)) from
      Iso.refl _) ≪≫
    (lowerStar AddCommGrpCat.{u + 1} f).mapIso
      ((forgetEvaluationIso X (Rrings l X) FX _ n ≪≫
        restrictionEvaluationAb l E X N n).symm)

private theorem transportAddSection {A B : AddCommGrpCat.{u + 1}} (e : A = B)
    (x : A) : HEq ((eqToHom e) x) x := by
  subst B
  rfl

private def rawPushMap
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    AddCommGrpCat.of ((g.push.obj N).val.obj (op (n, U.unop))) ⟶
      AddCommGrpCat.of (N.val.obj (op (n, (chart f U).unop))) :=
  AddCommGrpCat.ofHom
    (((g.ordinaryPushEvaluation n).hom.app N).val.app U).hom.toAddMonoidHom

private theorem restrictedPushLevel_hom
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    (restrictedPushLevel l E g FY FX N n).hom.hom.app U =
      eqToHom (FY.sections _ n U) ≫ rawPushMap l E g N n U ≫
        eqToHom (FX.sections _ n (chart f U)).symm := by
  rfl

private theorem restrictedPushLevel_sections
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((FY.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n)).obj.obj U) :
    HEq ((restrictedPushLevel l E g FY FX N n).hom.hom.app U x) x := by
  rw [restrictedPushLevel_hom]
  change HEq ((eqToHom (FX.sections
    ((SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E X)).obj N) n (chart f U)).symm)
    ((((g.ordinaryPushEvaluation n).hom.app N).val.app U)
      ((eqToHom (FY.sections
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E Y)).obj (g.push.obj N)) n U)) x))) x
  exact (transportAddSection _ _).trans
    ((pushEvaluationSections l E g n N U _).trans (transportAddSection _ x))

private theorem conjugatedSquare
    {A₀ A₁ B₀ B₁ A₀' A₁' B₀' B₁' : AddCommGrpCat.{u + 1}}
    (ea₀ : A₀ ≅ A₀') (ea₁ : A₁ ≅ A₁') (eb₀ : B₀ ≅ B₀') (eb₁ : B₁ ≅ B₁')
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (a' : A₀' ⟶ A₁') (b' : B₀' ⟶ B₁')
    (p₀ : A₀' ⟶ B₀') (p₁ : A₁' ⟶ B₁')
    (ha : a ≫ ea₁.hom = ea₀.hom ≫ a')
    (hb : b ≫ eb₁.hom = eb₀.hom ≫ b')
    (hp : a' ≫ p₁ = p₀ ≫ b') :
    a ≫ (ea₁.hom ≫ p₁ ≫ eb₁.inv) = (ea₀.hom ≫ p₀ ≫ eb₀.inv) ≫ b := by
  apply (Iso.cancel_iso_hom_right _ _ eb₁).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hb]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc a, ha]
  simp only [Category.assoc, hp]

private theorem rawTransition_apply
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{u + 1})
    (τ : ∀ k, B (k + 1) ⟶ B k)
    (M : SemilinearSections.Systems.{u + 1, u, u + 1} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : M.val.obj (op (m, U.unop))) :
    HEq (((SemilinearSections.transition.{u + 1, u, u + 1} J B τ h).app M).val.app U x)
      (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  unfold SemilinearSections.transition
  exact heq_of_eq (congr_heq
    ((SemilinearSections.transition_exists.{u + 1, u, u + 1} J B τ h).exists.choose_spec M U)
    (HEq.refl x))

private theorem sectionSquare
    {A₀ A₁ B₀ B₁ C₁ D₁ : Type u}
    (a : A₀ → A₁) (b : B₀ → B₁) (p₀ : A₀ → B₀) (p₁ : A₁ → B₁)
    (ta : A₀ → C₁) (tb : B₀ → D₁)
    (ha : ∀ x, HEq (ta x) (a x)) (hb : ∀ z, HEq (tb z) (b z))
    (hp : ∀ x y z, HEq (ta x) y → HEq (p₀ x) z → HEq (p₁ y) (tb z)) :
    ∀ x, p₁ (a x) = b (p₀ x) := by
  intro x
  exact eq_of_heq ((hp x (a x) (p₀ x) (ha x) HEq.rfl).trans (hb (p₀ x)))

private theorem rawPushMap_transition
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f) (N : Systems X (Arings l E X))
    {m n : ℕ} (h : n ≤ m) (U : Y.ProEtᵒᵖ) :
    (g.push.obj N).val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op ≫
        rawPushMap l E g N n U =
      rawPushMap l E g N m U ≫
        N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 (chart f U).unop)).op := by
  ext x
  change rawPushMap l E g N n U
      ((g.push.obj N).val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) =
    N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 (chart f U).unop)).op
      (rawPushMap l E g N m U x)
  exact sectionSquare
    (fun w ↦ (g.push.obj N).val.presheaf.map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op w)
    (fun w ↦ N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 (chart f U).unop)).op w)
    (fun w ↦ rawPushMap l E g N m U w) (fun w ↦ rawPushMap l E g N n U w)
    (fun w ↦ ((SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y)
      (SpTowerShriek.tau l E Y) h).app (g.push.obj N)).val.app U w)
    (fun w ↦ ((SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
      (SpTowerShriek.tau l E X) h).app N).val.app (chart f U) w)
    (rawTransition_apply (Scheme.ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) (g.push.obj N) h U)
    (rawTransition_apply (Scheme.ProEt.topology X)
      (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) N h (chart f U))
    (fun w y z hy hz ↦ pushHorizontal_sections l E g N h U w y hy z hz) x

private theorem restrictedPushLevel_transition
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (N : Systems X (Arings l E X)) {m n : ℕ} (h : n ≤ m) :
    (FY.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)).obj (g.push.obj N))).map (homOfLE h).op ≫
        (restrictedPushLevel l E g FY FX N n).hom =
      (restrictedPushLevel l E g FY FX N m).hom ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          ((FX.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E X)).obj N)).map (homOfLE h).op) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change _ ≫ (restrictedPushLevel l E g FY FX N n).hom.hom.app U =
    (restrictedPushLevel l E g FY FX N m).hom.hom.app U ≫ _
  rw [restrictedPushLevel_hom, restrictedPushLevel_hom]
  apply conjugatedSquare
    (eqToIso (FY.sections _ m U)) (eqToIso (FY.sections _ n U))
    (eqToIso (FX.sections _ m (chart f U))) (eqToIso (FX.sections _ n (chart f U)))
  · exact transport_addHom (FY.sections _ m U) (FY.sections _ n U) _ _
      (FY.transitions _ h U)
  · exact transport_addHom (FX.sections _ m (chart f U))
      (FX.sections _ n (chart f U)) _ _ (FX.transitions _ h (chart f U))
  · exact rawPushMap_transition l E g N h U

private theorem restrictedPushLevel_naturality
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    {N N' : Systems X (Arings l E X)} (a : N ⟶ N') (n : ℕ) :
    (FY.F.map ((SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)).map (g.push.map a))).app (op n) ≫
        (restrictedPushLevel l E g FY FX N' n).hom =
      (restrictedPushLevel l E g FY FX N n).hom ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          ((FX.F.map ((SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E X)).map a)).app (op n)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change _ ≫ (restrictedPushLevel l E g FY FX N' n).hom.hom.app U =
    (restrictedPushLevel l E g FY FX N n).hom.hom.app U ≫ _
  rw [restrictedPushLevel_hom, restrictedPushLevel_hom]
  apply conjugatedSquare
    (eqToIso (FY.sections _ n U)) (eqToIso (FY.sections _ n U))
    (eqToIso (FX.sections _ n (chart f U))) (eqToIso (FX.sections _ n (chart f U)))
  · exact transport_addHom (FY.sections _ n U) (FY.sections _ n U) _ _
      (FY.morphisms _ n U)
  · exact transport_addHom (FX.sections _ n (chart f U))
      (FX.sections _ n (chart f U)) _ _ (FX.morphisms _ n (chart f U))
  · ext x
    exact congrArg (fun k ↦ k.val.app U x)
      ((g.ordinaryPushEvaluation n).hom.naturality a)

private def restrictedPushIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
    (g : SpTowerShriek.Geometry l E b f)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X)) :
    (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)) ⋙ FY.F ≅
    (SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E X) ⋙ FX.F) ⋙ abPush f := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine NatIso.ofComponents
      (fun n ↦ restrictedPushLevel l E g FY FX N n.unop) ?_
    intro m n h
    change (FY.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)).obj (g.push.obj N))).map h ≫
        (restrictedPushLevel l E g FY FX N n.unop).hom =
      (restrictedPushLevel l E g FY FX N m.unop).hom ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map
          ((FX.F.obj ((SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E X)).obj N)).map h)
    have hh : (homOfLE (leOfHom h.unop)).op = h := by congr 1
    simpa only [hh] using restrictedPushLevel_transition l E g FY FX N (leOfHom h.unop)
  · intro N N' a
    apply NatTrans.ext
    funext n
    exact restrictedPushLevel_naturality l E g FY FX a n.unop

private def integralForgetFullyFaithful (T : Scheme.{u})
    (F : Forget T (Rrings l T)) : F.F.FullyFaithful := by
  let hl : LevelLinearity T (Rrings l T) := integral_sheaf_hom_linear l T
  let : F.F.Faithful := forgetFaithful T _ F
  let : F.F.Full := ⟨fun a ↦ ⟨forgetLift T _ F hl a, forgetLift_map T _ F hl a⟩⟩
  exact Functor.FullyFaithful.ofFullyFaithful F.F

section HomConstruction

variable {l E} {X Y : Scheme.{u}} {f : X ⟶ Y} {b : SpTowerShriek.Base l E}
  {g : SpTowerShriek.Geometry l E b f} {cY : Chern l E Y} {cX : Chern l E X}
  (d : IntegralCoefficientPullback l E f cY cX)
  (χ : (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F ≅
    (SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E X) ⋙ cX.reduction.forget.F) ⋙ abPush f)
  (hFY : cY.reduction.forget.F.FullyFaithful)
  (hFX : cX.reduction.forget.F.FullyFaithful)

private def restrictedHomEquiv (M : Systems Y (Rrings l Y))
    (N : Systems X (Arings l E X)) :
    (cX.scalar.model.E.obj (d.pull.obj M) ⟶ N) ≃
      (M ⟶ (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)).obj (g.push.obj N)) :=
  (cX.scalar.ordinaryAdjunction.homEquiv _ _).trans
    (hFX.homEquiv.trans
      ((Iso.homCongr (d.forgetIso.app M).symm (Iso.refl _)).trans
        (((abAdjunction f).homEquiv _ _).trans
          ((Iso.homCongr (Iso.refl _) (χ.app N).symm).trans hFY.homEquiv.symm))))

private theorem restrictedHomEquiv_spec (M : Systems Y (Rrings l Y))
    (N : Systems X (Arings l E X))
    (t : cX.scalar.model.E.obj (d.pull.obj M) ⟶ N) :
    cY.reduction.forget.F.map (restrictedHomEquiv d χ hFY hFX M N t) ≫ χ.hom.app N =
      (abAdjunction f).homEquiv _ _
        (d.forgetIso.hom.app M ≫ cX.reduction.forget.F.map
          ((cX.scalar.ordinaryAdjunction.homEquiv _ _) t)) := by
  simp [restrictedHomEquiv, Functor.FullyFaithful.homEquiv, Category.assoc]

private theorem restrictedHomEquiv_left
    {M' M : Systems Y (Rrings l Y)} {N : Systems X (Arings l E X)}
    (a : M' ⟶ M) (t : cX.scalar.model.E.obj (d.pull.obj M) ⟶ N) :
    restrictedHomEquiv d χ hFY hFX M' N
        ((d.pull ⋙ cX.scalar.model.E).map a ≫ t) =
      a ≫ restrictedHomEquiv d χ hFY hFX M N t := by
  apply hFY.map_injective
  apply (Iso.cancel_iso_hom_right _ _ (χ.app N)).1
  simp only [Iso.app_hom]
  rw [Functor.map_comp, Category.assoc, restrictedHomEquiv_spec,
    restrictedHomEquiv_spec, ← Adjunction.homEquiv_naturality_left]
  apply congrArg ((abAdjunction f).homEquiv _ _)
  change d.forgetIso.hom.app M' ≫ cX.reduction.forget.F.map
      ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
        (cX.scalar.model.E.map (d.pull.map a) ≫ t)) = _
  rw [Adjunction.homEquiv_naturality_left, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ cX.reduction.forget.F.map
    ((cX.scalar.ordinaryAdjunction.homEquiv _ _) t)) (d.forgetIso.hom.naturality a).symm

private theorem restrictedHomEquiv_right
    {M : Systems Y (Rrings l Y)} {N N' : Systems X (Arings l E X)}
    (t : cX.scalar.model.E.obj (d.pull.obj M) ⟶ N) (a : N ⟶ N') :
    restrictedHomEquiv d χ hFY hFX M N' (t ≫ a) =
      restrictedHomEquiv d χ hFY hFX M N t ≫
        (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E Y)).map a := by
  apply hFY.map_injective
  apply (Iso.cancel_iso_hom_right _ _ (χ.app N')).1
  simp only [Iso.app_hom]
  rw [Functor.map_comp, Category.assoc]
  change _ = cY.reduction.forget.F.map (restrictedHomEquiv d χ hFY hFX M N t) ≫
    ((g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F).map a ≫ χ.hom.app N'
  rw [χ.hom.naturality a, ← Category.assoc, restrictedHomEquiv_spec,
    restrictedHomEquiv_spec]
  rw [cX.scalar.ordinaryAdjunction.homEquiv_naturality_right t a,
    Functor.map_comp, ← Category.assoc,
    (abAdjunction f).homEquiv_naturality_right]
  rfl

private def restrictedAdjunction : (d.pull ⋙ cX.scalar.model.E) ⊣
    (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l E Y)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedHomEquiv d χ hFY hFX
      homEquiv_naturality_left_symm := by
        intro M' M N a t
        apply (restrictedHomEquiv d χ hFY hFX M' N).injective
        calc
          _ = a ≫ t := (restrictedHomEquiv d χ hFY hFX M' N).apply_symm_apply _
          _ = a ≫ restrictedHomEquiv d χ hFY hFX M N
              ((restrictedHomEquiv d χ hFY hFX M N).symm t) := by
            exact congrArg (fun k ↦ a ≫ k)
              ((restrictedHomEquiv d χ hFY hFX M N).apply_symm_apply t).symm
          _ = _ := (restrictedHomEquiv_left d χ hFY hFX a _).symm
      homEquiv_naturality_right := restrictedHomEquiv_right d χ hFY hFX }

private theorem restrictedAdjunction_spec (M : Systems Y (Rrings l Y))
    (N : Systems X (Arings l E X))
    (t : cX.scalar.model.E.obj (d.pull.obj M) ⟶ N) :
    cY.reduction.forget.F.map ((restrictedAdjunction d χ hFY hFX).homEquiv M N t) ≫
        χ.hom.app N =
      (abAdjunction f).homEquiv _ _
        (d.forgetIso.hom.app M ≫ cX.reduction.forget.F.map
          ((cX.scalar.ordinaryAdjunction.homEquiv _ _) t)) := by
  rw [restrictedAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact restrictedHomEquiv_spec d χ hFY hFX M N t

end HomConstruction

/-- The normalized restriction/direct-image square and its integral Hom adjunction.
This statement involves neither a coefficient-unit arrow nor a Tate-line comparison.

Source: blueprint latest, classes proof (2), balanced coefficient extension;
Stacks 03EL, ordinary module inverse image and scalar restriction.
(blueprint: lem-sp-tower-restricted-scalar-adjunction).

Proof: forget the scalar action on the given ordinary direct-image system. At
(n,U) it is the additive group of the original system at the base-changed chart.
The section, restriction and morphism equations of the two Forget records and
ordinaryPushEvaluation give identity-transport isomorphisms chi, natural in N.
For horizontal compatibility, transpose the system counit at each finite level.
Finite adjoint evaluation identifies its transpose with push-evaluation; the
normalized unit-transition equation identifies the two transition paths. Thus
these level isomorphisms assemble to whole abelian towers with the stated section
formula. For an R-system M and an
A-system N, forget an R-linear map d.pull(M) -> res(N), precompose with the
specified forgetIso, transpose under the componentwise abelian adjunction, and
postcompose with chi inverse. The resulting additive tower map is R-linear:
locally every section of the constant Z/ell^(n+1) ring sheaf lifts to a constant
integer, and additive maps commute with integer multiples. The local lifts
cover, so separatedness proves linearity on every chart. Forget is fully
faithful by the same argument. Thus this construction is a bijection of Hom
sets, natural in both arguments. Compose with the target ordinary scalar
adjunction to obtain the asserted adjunction a. Its Hom equivalence satisfies
exactly the displayed equation by construction.
No root object or Kummer map is used, and no coefficient flatness is required;
the local-lift argument also applies on empty charts and to zero rings. -/
theorem restrictedScalarAdjunction_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX) :
    ∃ χ : (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)) ⋙ cY.reduction.forget.F ≅
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E X) ⋙ cX.reduction.forget.F) ⋙ abPush f,
      (∀ (N : Systems X (Arings l E X)) (n : ℕ) (U : Y.ProEtᵒᵖ)
        (x : (((cY.reduction.forget.F.obj
          ((SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E Y)).obj (g.push.obj N))).obj (op n)).obj.obj U)),
        HEq ((((χ.hom.app N).app (op n)).hom.app U) x) x) ∧
      ∃ a : (d.pull ⋙ cX.scalar.model.E) ⊣
          (g.push ⋙ SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l E Y)),
        ∀ (M : Systems Y (Rrings l Y)) (N : Systems X (Arings l E X))
          (t : cX.scalar.model.E.obj (d.pull.obj M) ⟶ N),
          cY.reduction.forget.F.map ((a.homEquiv M N) t) ≫ χ.hom.app N =
            ((abAdjunction f).homEquiv _ _)
              (d.forgetIso.hom.app M ≫ cX.reduction.forget.F.map
                ((cX.scalar.ordinaryAdjunction.homEquiv _ _) t)) := by
  let χ := restrictedPushIso l E g cY.reduction.forget cX.reduction.forget
  refine ⟨χ, ?_, ?_⟩
  · intro N n U x
    change HEq ((restrictedPushLevel l E g cY.reduction.forget
      cX.reduction.forget N n).hom.hom.app U x) x
    exact restrictedPushLevel_sections l E g cY.reduction.forget cX.reduction.forget
      N n U x
  · let hFY := integralForgetFullyFaithful l Y cY.reduction.forget
    let hFX := integralForgetFullyFaithful l X cX.reduction.forget
    exact ⟨restrictedAdjunction d χ hFY hFX,
      restrictedAdjunction_spec d χ hFY hFX⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
