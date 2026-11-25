/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingTensorSupport
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # Open extension and the invertible normalized tensor transpose

Source: Zheng Construction 4.1; Stacks 03DI, 0E8I and 0GL1;
the system case of openTensorNormalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u v c r
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek
attribute [local implicit_reducible]
  AlgebraicGeometry.ProEtale.VaryingRing.push
  AlgebraicGeometry.ProEtale.spCoefficientCommRings
  AlgebraicGeometry.ProEtale.SpTowerShriek.tau
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.ProEtale.StrictTower.modulePullback
  AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage
  AlgebraicGeometry.ProEtale.StrictTower.constantRingIso
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
attribute [local irreducible] CategoryTheory.constantSheaf Padic
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  Padic.coefficientExtensionIntegers
  WeilConjectures.SemilinearSections.transition
  WeilConjectures.SemilinearSections.coefficientMap
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev chart {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEtᵒᵖ) :=
  (Scheme.proEtaleBaseChange f).op.obj U

private def restrictedSection {C : Type*} [Category C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    (M : SemilinearSections.Mod.{_, _, v} J S) (U : Cᵒᵖ) :
    ((SemilinearSections.res.{_, _, v} φ).obj M).val.obj U → M.val.obj U :=
  fun x ↦ x

private theorem restrictedSection_heq {C : Type*} [Category C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    (M : SemilinearSections.Mod.{_, _, v} J S) (U : Cᵒᵖ)
    (x : ((SemilinearSections.res.{_, _, v} φ).obj M).val.obj U) :
    HEq (restrictedSection φ M U x) x := by rfl

private theorem restrict_map_heq {C : Type*} [Category C] [EssentiallySmall.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{v}} (φ : R ⟶ S)
    {M N : SemilinearSections.Mod.{_, _, v} J S} (a : M ⟶ N) (U : Cᵒᵖ)
    (x : ((SemilinearSections.res.{_, _, v} φ).obj M).val.obj U)
    (y : M.val.obj U) (h : HEq x y) :
    HEq (((SemilinearSections.res.{_, _, v} φ).map a).val.app U x)
      (a.val.app U y) := by
  have hx : x = y := eq_of_heq h
  cases hx
  rfl

private def pushSection (A : Type u) [CommRing A] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (U : S.ProEtᵒᵖ) :
    ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U →
      M.val.obj (chart f U) := fun x ↦ x

private theorem pushSection_heq (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (U : S.ProEtᵒᵖ) (x : ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U) :
    HEq (pushSection A f M U x) x := by rfl

private theorem pushSection_map (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) {M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)}
    (a : M ⟶ N) (U : S.ProEtᵒᵖ)
    (x : ((Scheme.proEtaleConstantRingPushforward A f).obj M).val.obj U) :
    pushSection A f N U (((Scheme.proEtaleConstantRingPushforward A f).map a).val.app U x) =
      a.val.app (chart f U) (pushSection A f M U x) := by rfl
private theorem pushSection_comp (A : Type u) [CommRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) {M N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)}
    {P : Scheme.proEtaleRingModules S (Scheme.proEtaleConstantRing S A)}
    (a : P ⟶ (Scheme.proEtaleConstantRingPushforward A f).obj M) (b : M ⟶ N)
    (U : S.ProEtᵒᵖ) (x : P.val.obj U) :
    pushSection A f N U ((a ≫ (Scheme.proEtaleConstantRingPushforward A f).map b).val.app U x) =
      b.val.app (chart f U) (pushSection A f M U (a.val.app U x)) := by rfl

private theorem counit_evaluation
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    {L : A ⥤ B} {R : B ⥤ A} (b : L ⊣ R) (V : C ⥤ A) (W : D ⥤ B)
    (eF : F ⋙ W ≅ V ⋙ L) (eG : G ⋙ V ≅ W ⋙ R)
    (hu : ∀ M, V.map (a.unit.app M) ≫ eG.hom.app (F.obj M) ≫
      R.map (eF.hom.app M) = b.unit.app (V.obj M)) (N : D) :
    b.homEquiv _ _ (eF.inv.app (G.obj N) ≫ W.map (a.counit.app N)) =
      eG.hom.app N := by
  have hu' : V.map (a.unit.app (G.obj N)) ≫ eG.hom.app (F.obj (G.obj N)) =
      b.unit.app (V.obj (G.obj N)) ≫ R.map (eF.inv.app (G.obj N)) := by
    apply (Iso.eq_comp_inv (R.mapIso (eF.app (G.obj N)))).2
    simpa only [CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      using hu (G.obj N)
  have hh : V.map (a.homEquiv _ _ (a.counit.app N)) ≫ eG.hom.app N =
      b.homEquiv _ _ (eF.inv.app (G.obj N) ≫ W.map (a.counit.app N)) := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, Category.assoc]
    have hn : V.map (G.map (a.counit.app N)) ≫ eG.hom.app N =
        eG.hom.app (F.obj (G.obj N)) ≫ R.map (W.map (a.counit.app N)) :=
      eG.hom.naturality (a.counit.app N)
    rw [hn, ← Category.assoc, hu']
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
      Category.assoc]
  have he : a.homEquiv _ _ (a.counit.app N) = 𝟙 (G.obj N) := by
    rw [← a.homEquiv_symm_id N]
    exact (a.homEquiv _ _).apply_symm_apply _
  rw [he, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  exact hh.symm

private abbrev horizontal (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    SpTowerShriek.ev l E T m ⟶ SpTowerShriek.ev l E T n ⋙
      SemilinearSections.res.{u + 1, u, u + 1}
        (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h) :=
  SemilinearSections.transition.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h
private abbrev restrict (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T m) :=
  SemilinearSections.res.{u + 1, u, u + 1}
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)

private def horizontalSection (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : SpTowerShriek.S l E T) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T m).obj M).val.obj U) :
    ((SpTowerShriek.ev l E T n).obj M).val.obj U :=
  restrictedSection
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    ((SpTowerShriek.ev l E T n).obj M) U (((horizontal l E T h).app M).val.app U x)

private theorem push_horizontal {X S : Scheme.{u}} (f : X ⟶ S)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (N : SpTowerShriek.S l E X) {m n : ℕ} (h : n ≤ m) (U : S.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E S m).obj (g.push.obj N)).val.obj U) :
    pushSection (SpTowerShriek.R l E n) f ((SpTowerShriek.ev l E X n).obj N) U
      (((g.ordinaryPushEvaluation n).hom.app N).val.app U
        (horizontalSection l E S h (g.push.obj N) U x)) =
      horizontalSection l E X h N (chart f U)
        (pushSection (SpTowerShriek.R l E m) f ((SpTowerShriek.ev l E X m).obj N) U
          (((g.ordinaryPushEvaluation m).hom.app N).val.app U x)) := by
  let D := g.push.obj N
  let ε : g.pull.obj D ⟶ N := g.ordinaryAdjunction.counit.app N
  let a := fun k ↦ Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E k) f
  let d := fun k ↦ (g.ordinaryPullEvaluation k).inv.app D ≫
    (SpTowerShriek.ev l E X k).map ε
  have hd (k : ℕ) : (a k).homEquiv _ _ (d k) =
      (g.ordinaryPushEvaluation k).hom.app N := by
    exact counit_evaluation g.ordinaryAdjunction (a k)
      (SpTowerShriek.ev l E S k) (SpTowerShriek.ev l E X k)
      (g.ordinaryPullEvaluation k) (g.ordinaryPushEvaluation k)
      (SpTowerShriek.geometry_unit_evaluation l E b g k) N
  let t := (g.ordinaryPullEvaluation m).inv.app D ≫
    (horizontal l E X h).app (g.pull.obj D) ≫
      (restrict l E X h).map ((g.ordinaryPullEvaluation n).hom.app D)
  have ht : t ≫ (restrict l E X h).map (d n) =
      d m ≫ (horizontal l E X h).app N := by
    calc
      _ = (g.ordinaryPullEvaluation m).inv.app D ≫
          (horizontal l E X h).app (g.pull.obj D) ≫
            (restrict l E X h).map
              ((g.ordinaryPullEvaluation n).hom.app D ≫ d n) := by
        simp only [t, Category.assoc, CategoryTheory.Functor.map_comp]
      _ = (g.ordinaryPullEvaluation m).inv.app D ≫
          (horizontal l E X h).app (g.pull.obj D) ≫
            (restrict l E X h).map ((SpTowerShriek.ev l E X n).map ε) := by
        rw [show (g.ordinaryPullEvaluation n).hom.app D ≫ d n =
          (SpTowerShriek.ev l E X n).map ε from
            (g.ordinaryPullEvaluation n).hom_inv_id_app_assoc D _]
      _ = _ := congrArg ((g.ordinaryPullEvaluation m).inv.app D ≫ ·)
        ((horizontal l E X h).naturality ε).symm
  let y := horizontalSection l E S h D U x
  have hy : HEq (((horizontal l E S h).app D).val.app U x) y :=
    (restrictedSection_heq _ _ _ _).symm
  have hu := g.ordinaryUnitTransition
  unfold SpTowerShriek.OrdinaryUnitTransition SpTowerShriek.OrdinaryUnitTransitionModel at hu
  have hh := hu D h U x y hy
  have hh' : HEq
      (pushSection (SpTowerShriek.R l E m) f ((restrict l E X h).obj
        ((SpTowerShriek.ev l E X n).obj N)) U
          (((a m).homEquiv _ _ (t ≫ (restrict l E X h).map (d n))).val.app U x))
      (pushSection (SpTowerShriek.R l E n) f ((SpTowerShriek.ev l E X n).obj N) U
        (((a n).homEquiv _ _ (d n)).val.app U y)) := by
    rw [Adjunction.homEquiv_naturality_right, pushSection_comp]
    have hh₀ := (pushSection_heq _ _ _ _ _).trans
      (hh.trans (pushSection_heq _ _ _ _ _).symm)
    have hh₁ := restrict_map_heq
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h)
      (d n) (chart f U) _ _ hh₀
    change HEq _ (pushSection (SpTowerShriek.R l E n) f _ U
      (((a n).unit.app _ ≫
        (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
          (d n)).val.app U y))
    rw [show ((a n).unit.app _ ≫
        (Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
          (d n)).val.app U y =
        ((Scheme.proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
          (d n)).val.app U (((a n).unit.app _).val.app U y) by rfl,
      pushSection_map]
    exact hh₁
  rw [ht, Adjunction.homEquiv_naturality_right, hd m, hd n, pushSection_comp] at hh'
  exact eq_of_heq (((restrictedSection_heq _ _ _ _).trans hh').symm)

private theorem inverseMate_rightIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {P Q : D ⥤ C} {F' : C' ⥤ D'} {P' : D' ⥤ C'}
    (a : F ⊣ P) (b : F' ⊣ P') (e : P ≅ Q)
    {V : C ⥤ C'} {W : D ⥤ D'} (d : Q ⋙ V ⟶ W ⋙ P') :
    ((mateEquiv (a.ofNatIsoRight e) b).symm d) =
      ((mateEquiv a b).symm (Functor.whiskerRight e.hom V ≫ d)) := by
  ext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h₁ := unit_mateEquiv_symm (a.ofNatIsoRight e) b (TwoSquare.mk _ _ _ _ d) M
  have h₂ := unit_mateEquiv_symm a b
    (TwoSquare.mk _ _ _ _ (Functor.whiskerRight e.hom V ≫ d)) M
  simp only [Functor.id_obj] at h₁ h₂
  calc
    _ = V.map ((a.ofNatIsoRight e).unit.app M) ≫ d.app (F.obj M) := h₁.symm
    _ = V.map (a.unit.app M) ≫
        (Functor.whiskerRight e.hom V ≫ d).app (F.obj M) := by
      simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
        CategoryTheory.Functor.map_comp, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Category.assoc]
    _ = _ := h₂

section ExactUnit

-- Work over abstract abelian categories so the localization formula retains its instances.
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard

end ExactUnit

private abbrev SS (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n) :=
  SemilinearSections.Systems.{u + 1, u, u + 1} (ProEt.topology X) (B l E X) σ
private abbrev EE (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (B l E X) σ
private abbrev DD (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n) :=
  SemilinearSections.DS.{u + 1, u, u + 1} (ProEt.topology X) (B l E X) σ
private def transitionValue {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B' : ℕ → Sheaf J CommRingCat.{r})
    (σ : ∀ n, B' (n + 1) ⟶ B' n) {m n : ℕ} (h : n ≤ m)
    (M : SemilinearSections.Systems.{c, v, r} J B' σ) (V : Cᵒᵖ)
    (x : ((SemilinearSections.evaluation.{c, v, r} J B' σ m).obj M).val.obj V) :
    ((SemilinearSections.evaluation.{c, v, r} J B' σ n).obj M).val.obj V :=
  ((SemilinearSections.transition.{c, v, r} J B' σ h).app M).val.app V x

private theorem transitionValue_eq {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B' : ℕ → Sheaf J CommRingCat.{r})
    (σ : ∀ n, B' (n + 1) ⟶ B' n) {m n : ℕ} (h : n ≤ m)
    (M : SemilinearSections.Systems.{c, v, r} J B' σ) (V : Cᵒᵖ)
    (x : ((SemilinearSections.evaluation.{c, v, r} J B' σ m).obj M).val.obj V) :
    transitionValue J B' σ h M V x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x := by
  unfold transitionValue SemilinearSections.transition
  exact congrFun (eq_of_heq
    ((SemilinearSections.transition_exists.{c, v, r} J B' σ h).exists.choose_spec M V)) x

private abbrev HS (X : Scheme.{u}) (σ : ∀ n, B l E X (n + 1) ⟶ B l E X n)
    {m n : ℕ} (h : n ≤ m) :=
  transitionValue (ProEt.topology X) (B l E X) σ h

-- Each section comparison normalizes the two continuous module-sheaf carrier presentations.
private theorem canonicalPushHorizontal
    (R' : ℕ → CommRingCat.{u + 1}) (φ : ∀ n, R' (n + 1) ⟶ R' n)
    {U T : Scheme.{u}} (j : U ⟶ T) (M : VaryingRing.Modules R' φ U)
    {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ)
    (x : ((VaryingRing.eval R' φ T m).obj ((VaryingRing.push R' φ j).obj M)).val.obj V) :
    ((VaryingRing.moduleEvalP R' φ j n).hom.app M).val.app V
        (transitionValue (ProEt.topology T) (VaryingRing.coefficients R' T)
          (VaryingRing.coefficientTransition R' φ T) h ((VaryingRing.push R' φ j).obj M) V x) =
      transitionValue (ProEt.topology U) (VaryingRing.coefficients R' U)
        (VaryingRing.coefficientTransition R' φ U) h M (chart j V)
          (((VaryingRing.moduleEvalP R' φ j m).hom.app M).val.app V x) := by
  dsimp only [VaryingRing.moduleEvalP]
  have hn := (VaryingRing.moduleEvalP_existsUnique R' φ j n).choose_spec.1 M V.unop
    (transitionValue (ProEt.topology T) (VaryingRing.coefficients R' T)
      (VaryingRing.coefficientTransition R' φ T) h ((VaryingRing.push R' φ j).obj M) V x)
  have hm := (VaryingRing.moduleEvalP_existsUnique R' φ j m).choose_spec.1 M V.unop x
  -- Apply the section equalities directly to avoid rewrite matching through carrier conversions.
  refine hn.trans ?_
  refine Eq.trans ?_ (congrArg
    (transitionValue (ProEt.topology U) (VaryingRing.coefficients R' U)
      (VaryingRing.coefficientTransition R' φ U) h M (chart j V)) hm.symm)
  simp only [transitionValue_eq]
  change M.val.map
    (((VaryingRing.baseChange j).map (Prod.mkHom (homOfLE h) (𝟙 V.unop))).op) x =
    M.val.map
      (Prod.mkHom (homOfLE h) (𝟙 ((Scheme.proEtaleBaseChange j).obj V.unop))).op x
  apply M.val.congr_map_apply
  congr 1
  simp only [VaryingRing.baseChange, Functor.prod_map, Functor.id_map,
    CategoryTheory.Functor.map_id]

-- A private model records the canonical operations without imposing a definitional
-- choice of the adjacent coefficient maps. This permits equality transport once.
private structure OpenSiteModel (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j]
    (σU : ∀ n, B l E U (n + 1) ⟶ B l E U n)
    (σT : ∀ n, B l E T (n + 1) ⟶ B l E T n) where
  push : SS l E U σU ⥤ SS l E T σT
  pull : SS l E T σT ⥤ SS l E U σU
  extension : SS l E U σU ⥤ SS l E T σT
  [pullAdditive : pull.Additive]
  [pullLimits : PreservesFiniteLimits pull]
  [pullColimits : PreservesFiniteColimits pull]
  [extensionAdditive : extension.Additive]
  [extensionLimits : PreservesFiniteLimits extension]
  [extensionColimits : PreservesFiniteColimits extension]
  adj : pull ⊣ push
  openAdj : extension ⊣ pull
  evalP : ∀ n, push ⋙ EE l E T σT n ≅
    EE l E U σU n ⋙ proEtaleConstantRingPushforward (R l E n) j
  pushHorizontal : ∀ (M : SS l E U σU) {m n : ℕ} (h : n ≤ m) (V : T.ProEtᵒᵖ)
    (x : ((EE l E T σT m).obj (push.obj M)).val.obj V),
    ((evalP n).hom.app M).val.app V (HS l E T σT h (push.obj M) V x) =
      HS l E U σU h M (chart j V) (((evalP m).hom.app M).val.app V x)
  evalG : ∀ n, pull ⋙ EE l E U σU n ≅
    EE l E T σT n ⋙ proEtaleConstantRingPullback (R l E n) j
  unitG : ∀ n (M : SS l E T σT),
    (EE l E T σT n).map (adj.unit.app M) ≫
      (evalP n).hom.app (pull.obj M) ≫
      (proEtaleConstantRingPushforward (R l E n) j).map ((evalG n).hom.app M) =
        (proEtaleConstantRingAdjunction (R l E n) j).unit.app ((EE l E T σT n).obj M)
  openMate : ∀ n, IsIso
    ((mateEquiv openAdj (finiteOpenAdjunction l E b j n)).symm (evalG n).hom)
  openUnit : IsIso openAdj.unit
  support : ∀ (A : SemilinearSections.Closed.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing (ProEt.topology T) (B l E T) σT))
    (_ : SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing (ProEt.topology T) (B l E T) σT) A)
    (M : DD l E U σU) (N : DD l E T σT),
    extension.mapDerivedCategory.essImage
      (A.tensor.obj (extension.mapDerivedCategory.obj M, N))

attribute [local instance] OpenSiteModel.pullAdditive OpenSiteModel.pullLimits
  OpenSiteModel.pullColimits OpenSiteModel.extensionAdditive OpenSiteModel.extensionLimits
  OpenSiteModel.extensionColimits

private theorem openMate_isIso (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (g : Geometry l E b j)
    (c : OpenSiteModel l E b j (tau l E U) (tau l E T))
    (p : c.pull ≅ g.pull)
    (hp : ∀ n : ℕ, Functor.isoWhiskerRight p (ev l E U n) ≪≫
      g.ordinaryPullEvaluation n = c.evalG n) (n : ℕ) :
    IsIso ((mateEquiv (c.openAdj.ofNatIsoRight p)
      (finiteOpenAdjunction l E b j n)).symm (g.ordinaryPullEvaluation n).hom) := by
  rw [inverseMate_rightIso]
  have he : Functor.whiskerRight p.hom (ev l E U n) ≫
      (g.ordinaryPullEvaluation n).hom = (c.evalG n).hom := congrArg Iso.hom (hp n)
  rw [he]
  exact c.openMate n

end AlgebraicGeometry.ProEtale.SpTowerShriek
