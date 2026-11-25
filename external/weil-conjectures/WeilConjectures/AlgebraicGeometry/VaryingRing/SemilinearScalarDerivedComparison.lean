/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarOrdinaryComparison
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarOrdinaryAlphaNormalization
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaPullback

/-! # Specified derived scalar comparisons

Source: Stacks Project, Tags 03D7, 07A6, 0D6D, 0D6E and 04VG;
blueprint fix-prop-coherence, coefficient comparisons of units and counits
(blueprint: lem-sf-semilinear-scalar-derived-comparison).

Localize the given normalized ordinary package. The direct-image map is its actual
adjunction mate. Its evaluation and the intrinsic proper/open alpha equation are
statements about these specified transformations on unbounded derived system categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w x
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The inverse-face cube follows by injectivity of transposition.
private theorem scalarInverseMateEqOfUnit
    {A B C D : Type u} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {P : B ⥤ A} {F' : C ⥤ D} {P' : D ⥤ C}
    (a : F ⊣ P) (b : F' ⊣ P') (E : A ⥤ C) (E' : B ⥤ D)
    (d : P ⋙ E ⟶ E' ⋙ P') (q : F ⋙ E' ≅ E ⋙ F')
    (hq : ∀ N, E.map (a.unit.app N) ≫ d.app (F.obj N) ≫
      P'.map (q.hom.app N) = b.unit.app (E.obj N)) :
    ((mateEquiv a b).symm d) = q.inv := by
  apply NatTrans.ext
  funext N
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu : E.map (a.unit.app N) ≫ d.app (F.obj N) =
      b.unit.app (E.obj N) ≫ P'.map (((mateEquiv a b).symm d).app N) :=
    unit_mateEquiv_symm a b d N
  rw [← hu]
  apply (cancel_mono (P'.map (q.hom.app N))).mp
  simp only [Category.assoc]
  rw [← P'.map_comp, Iso.inv_hom_id_app]
  exact (hq N).trans ((congrArg (fun z ↦ b.unit.app (E.obj N) ≫ z)
    (P'.map_id _)).trans (Category.comp_id _)).symm

private theorem inverseMateCube
    {A B C D E F H I : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category E] [Category F] [Category H] [Category I]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E} {L₄ : H ⥤ I} {R₄ : I ⥤ H}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    {G : A ⥤ C} {G' : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {J : A ⥤ H} {J' : H ⥤ E} {K : B ⥤ I} {K' : I ⥤ F}
    (α : TwoSquare G L₁ L₂ H₁) (β : TwoSquare G' L₂ L₃ H₂)
    (γ : TwoSquare J L₁ L₄ K) (δ : TwoSquare J' L₄ L₃ K')
    (p : G ⋙ G' ≅ J ⋙ J') (q : H₁ ⋙ H₂ ≅ K ⋙ K')
    (hc : ∀ N : B,
      G'.map ((mateEquiv a₁ a₂ α).app N) ≫
          (mateEquiv a₂ a₃ β).app (H₁.obj N) ≫ R₃.map (q.hom.app N) =
        p.hom.app (R₁.obj N) ≫ J'.map ((mateEquiv a₁ a₄ γ).app N) ≫
          (mateEquiv a₄ a₃ δ).app (K.obj N)) :
    ∀ M : A,
      β.app (G.obj M) ≫ H₂.map (α.app M) ≫ q.hom.app (L₁.obj M) =
        L₃.map (p.hom.app M) ≫ δ.app (J.obj M) ≫ K'.map (γ.app M) := by
  have he :
      ((((TwoSquare.hComp α β).whiskerTop (𝟙 _)).whiskerBottom q.hom)) =
        (((TwoSquare.hComp γ δ).whiskerTop p.hom).whiskerBottom (𝟙 _)) := by
    apply (mateEquiv a₁ a₃).injective
    rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_whiskerTop_whiskerBottom,
      mateEquiv_vcomp a₁ a₂ a₃, mateEquiv_vcomp a₁ a₄ a₃]
    ext N
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
      Category.id_comp, Category.assoc,
      Functor.comp_obj]
    erw [R₃.map_id]
    simpa only [Category.comp_id, Category.assoc] using hc N
  intro M
  have hm := congrArg (fun z ↦ z.app M) he
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc, CategoryTheory.Functor.map_id,
    TwoSquare.mk, Functor.comp_obj] using hm

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable {R : ℕ → CommRingCat.{u + 1}} {φ : ∀ n : ℕ, R (n + 1) ⟶ R n}
  {B : Type (u + 1)} [CommRing B] {ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n}
  (D : OrdinaryScalarComparison R φ B ψ)

/-- Additivity supplied by ordinary scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
instance scalarRhoAdditive (X : Scheme.{u}) : (D.rho X).Additive := D.additive X

/-- Left exactness supplied by ordinary scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
instance scalarRhoLimits (X : Scheme.{u}) : PreservesFiniteLimits (D.rho X) := D.limits X

/-- Right exactness supplied by ordinary scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
instance scalarRhoColimits (X : Scheme.{u}) : PreservesFiniteColimits (D.rho X) := D.colimits X

/-- Termwise localization of the actual sectionwise restriction. Source: Stacks 04VG
(blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
abbrev scalarRho (X : Scheme.{u}) : Derived R φ X ⥤ StrictTower.Derived B X :=
  (D.rho X).mapDerivedCategory

/-- Exact localization of the specified ordinary inverse-image comparison.
Source: Stacks 04VG (blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
def scalarB {X Y : Scheme.{u}} (f : X ⟶ Y) :
    G R φ f ⋙ scalarRho D X ≅ scalarRho D Y ⋙ StrictTower.G B f :=
  Functor.mapDerivedCategoryCompIso (pull R φ f) (D.rho X) ≪≫
    Functor.mapDerivedCategoryNatIso (D.b f) ≪≫
      (Functor.mapDerivedCategoryCompIso (D.rho Y) (StrictTower.towerPullback B f)).symm

/-- The specified unit--inverse-b--counit mate, with no choice of a direct-image map.
Source: Stacks 07A6 (blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
def scalarD {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P R φ f ⋙ scalarRho D Y ⟶ scalarRho D X ⋙ StrictTower.R B f :=
  (mateEquiv (adj R φ f) (StrictTower.adj B f) (scalarB D f).inv)

/-- Exact localization of the ordinary open comparison, retaining its open units.
Source: Stacks 03DI, 04VG (blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
def scalarA {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J R φ j ⋙ scalarRho D X ≅ scalarRho D U ⋙ StrictTower.J B j :=
  Functor.mapDerivedCategoryCompIso (extension R φ j) (D.rho X) ≪≫
    Functor.mapDerivedCategoryNatIso (D.a j) ≪≫
      (Functor.mapDerivedCategoryCompIso (D.rho U) (StrictTower.towerJ B j)).symm

attribute [local instance] WeilConjectures.sfAbBijective

/-- The evaluation identification is the localization of the given identity on sections.
Source: Stacks 04VG (blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
def scalarLevel (X : Scheme.{u}) (n : ℕ) :
    scalarRho D X ⋙ StrictTower.ev B X n ≅
      ev R φ X n ⋙
        resD.{u + 1, u, u + 1} (ordinaryScalarMap R B ψ X n) :=
  Functor.mapDerivedCategoryCompIso (D.rho X)
    ((evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := D.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n))
      (G := eval R φ X n ⋙
        res.{u + 1, u, u + 1} (ordinaryScalarMap R B ψ X n)) (D.level X n) ≪≫
      (Functor.mapDerivedCategoryCompIso (eval R φ X n)
        (res.{u + 1, u, u + 1} (ordinaryScalarMap R B ψ X n))).symm

/-- The level direct-image comparison is precisely the recorded normalized ring-change
comparison. Source: Stacks 0D6E (blueprint: lem-sf-semilinear-scalar-derived-comparison). -/
def scalarLevelD {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm

private def scalarLevelDOrd {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm

section OrdinarySections
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 128

private abbrev unrestrictSection {X : Scheme.{u}}
    {A S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : A ⟶ S)
    (N : Scheme.proEtaleRingModules X S) (H : X.ProEtᵒᵖ)
    (x : ((res a).obj N).val.obj H) : N.val.obj H := x

private abbrev evalSection (X : Scheme.{u}) (n : ℕ) (N : Modules R φ X)
    (H : X.ProEtᵒᵖ) (x : ((eval R φ X n).obj N).val.obj H) :
    N.val.obj (op (n, H.unop)) := by
  dsimp only [eval, WeilConjectures.SemilinearSections.evaluation,
    SheafOfModules.pushforward_obj_val,
    PresheafOfModules.pushforward_obj_obj, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.obj'] at x
  exact x

private abbrev directSection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : StrictTower.Modules (R n) X) (H : Y.ProEtᵒᵖ)
    (x : ((StrictTower.moduleDirectImage (R n) f).obj N).val.obj H) :
    N.val.obj ((Scheme.proEtaleBaseChange f).op.obj H) := x

private theorem scalarLevelDOrd_sections {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : StrictTower.Modules (R n) X) (H : Y.ProEtᵒᵖ)
    (x : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj H)) :
    (((scalarLevelDOrd (R := R) (B := B) (ψ := ψ) f n).hom.app N).val.app H) x = x :=
  (Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm).choose_spec.1 N H x

attribute [local irreducible] constantSheaf presheafToSheaf systemRing rings

-- All three ordinary comparisons are the identity on the same sections.
private theorem scalarDOrd_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : Modules R φ X) :
    ((D.d f).hom.app N).app (op n) ≫
        (StrictTower.moduleDirectImage B f).map ((D.level X n).hom.app N) =
      (D.level Y n).hom.app ((push R φ f).obj N) ≫
        (res (ordinaryScalarMap R B ψ Y n)).map ((moduleEvalP R φ f n).hom.app N) ≫
        (scalarLevelDOrd (R := R) (B := B) (ψ := ψ) f n).hom.app
          ((eval R φ X n).obj N) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro H
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hd := D.d_sections f N n H x
  have hlX := D.level_sections X n N
    ((Scheme.proEtaleBaseChange f).op.obj H)
      (((((D.d f).hom.app N).app (op n)).val.app H) x)
  have hlY := D.level_sections Y n ((push R φ f).obj N) H x
  have hp := (moduleEvalP_existsUnique R φ f n).choose_spec.1
  let z := unrestrictSection (ordinaryScalarMap R B ψ Y n)
    ((eval R φ Y n).obj ((push R φ f).obj N)) H
    (((D.level Y n).hom.app ((push R φ f).obj N)).val.app H x)
  let w := directSection f n ((eval R φ X n).obj N) H
    ((((moduleEvalP R φ f n).hom.app N).val.app H) z)
  have hq'' := scalarLevelDOrd_sections (R := R) (B := B) (ψ := ψ) f n
    ((eval R φ X n).obj N) H w
  have hp' := hp N H.unop (evalSection Y n ((push R φ f).obj N) H z)
  change (((D.level X n).hom.app N).val.app
      ((Scheme.proEtaleBaseChange f).op.obj H)
      (((((D.d f).hom.app N).app (op n)).val.app H) x)) =
    (((scalarLevelDOrd (R := R) (B := B) (ψ := ψ) f n).hom.app
      ((eval R φ X n).obj N)).val.app H w)
  have hright : HEq
      (((scalarLevelDOrd (R := R) (B := B) (ψ := ψ) f n).hom.app
        ((eval R φ X n).obj N)).val.app H w) x :=
    (heq_of_eq (hq''.trans hp')).trans hlY
  apply eq_of_heq
  exact (hlX.trans hd).trans hright.symm

end OrdinarySections

private theorem scalarEvalP_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (moduleAdj R φ f)
      (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
        (coefficients R X n) (StrictTower.constantRingIso (R n) f))
      (moduleEvalG R φ f n).inv) = (moduleEvalP R φ f n).hom := by
  have hq := scalarInverseMateEqOfUnit (moduleAdj R φ f)
    (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
      (coefficients R X n) (StrictTower.constantRingIso (R n) f))
    (eval R φ Y n) (eval R φ X n) (moduleEvalP R φ f n).hom
    (moduleEvalG R φ f n) (moduleEvalG_existsUnique R φ f n).choose_spec.1
  have hh : (mateEquiv (moduleAdj R φ f)
      (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
        (coefficients R X n) (StrictTower.constantRingIso (R n) f))).symm
      (TwoSquare.mk _ _ _ _ (moduleEvalP R φ f n).hom) =
        TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv := by
    exact hq
  exact ((Equiv.eq_symm_apply _).1 hh.symm)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarTowerEvaluation_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv
      ((Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
        (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).whiskerRight ℕᵒᵖ)
      (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
        (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (eqToIso (StrictTower.evaluationPullback B f n)).inv)) =
        𝟙 ((evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) ⋙
          StrictTower.moduleDirectImage B f) := by
  apply NatTrans.ext
  funext T
  change (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
    (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).unit.app
        ((StrictTower.moduleDirectImage B f).obj (T.obj (op n))) ≫
      (StrictTower.moduleDirectImage B f).map
        ((Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
          (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).counit.app
            (T.obj (op n))) = 𝟙 _
  exact (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
    (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).right_triangle_components _

private theorem scalarOrdinaryInverseCube {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (hd : ∀ N : Modules R φ X,
      ((D.d f).hom.app N).app (op n) ≫
          (StrictTower.moduleDirectImage B f).map ((D.level X n).hom.app N) =
        (D.level Y n).hom.app ((push R φ f).obj N) ≫
          (res (ordinaryScalarMap R B ψ Y n)).map ((moduleEvalP R φ f n).hom.app N) ≫
          (scalarLevelDOrd (R := R) (B := B) (ψ := ψ) f n).hom.app
            ((eval R φ X n).obj N)) (M : Modules R φ Y) :
    (eqToIso (StrictTower.evaluationPullback B f n)).inv.app ((D.rho Y).obj M) ≫
        ((evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n)).map
          ((D.b f).inv.app M) ≫ (D.level X n).hom.app ((pull R φ f).obj M) =
      (StrictTower.modulePullback B f).map ((D.level Y n).hom.app M) ≫
        (Scheme.proEtaleRingRestrictionPullbackInv f
          (StrictTower.coefficients B Y) (coefficients R Y n)
          (StrictTower.coefficients B X) (coefficients R X n)
          (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
          (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
          (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm).app
            ((eval R φ Y n).obj M) ≫
        (res (ordinaryScalarMap R B ψ X n)).map ((moduleEvalG R φ f n).inv.app M) := by
  apply inverseMateCube (moduleAdj R φ f) (scalarTowerAdj B f)
    (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
    (Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
      (coefficients R X n) (StrictTower.constantRingIso (R n) f))
    (TwoSquare.mk _ _ _ _ (D.b f).inv)
    (TwoSquare.mk _ _ _ _ (eqToIso (StrictTower.evaluationPullback B f n)).inv)
    (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv)
    (TwoSquare.mk _ _ _ _
      (Scheme.proEtaleRingRestrictionPullbackInv f
        (StrictTower.coefficients B Y) (coefficients R Y n)
        (StrictTower.coefficients B X) (coefficients R X n)
        (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
        (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
        (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm))
    (D.level Y n) (D.level X n) ?_ M
  intro N
  have h1 := congr_app (D.mate f) N
  have h2 := congr_app (scalarTowerEvaluation_mate (B := B) f n) ((D.rho X).obj N)
  have h3 := congr_app (scalarEvalP_mate (R := R) (φ := φ) f n) N
  have h4 := congr_app (Scheme.restrictionPullback_mate f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm)
      ((eval R φ X n).obj N)
  rw [h1]
  dsimp only [TwoSquare.mk] at h2 h3 h4 ⊢
  have h2' : (mateEquiv (scalarTowerAdj B f)
      (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
        (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
      (TwoSquare.mk _ _ _ _ (eqToIso (StrictTower.evaluationPullback B f n)).inv)).app
        ((D.rho X).obj N) = 𝟙 _ := h2
  have hL := congrArg (fun z ↦
    ((evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n)).map
      ((D.d f).hom.app N) ≫ z ≫
        (StrictTower.moduleDirectImage B f).map ((D.level X n).hom.app N)) h2'
  dsimp only [Functor.id_obj, Functor.comp_obj] at hL
  erw [Category.id_comp] at hL
  have hR := congrArg₂ (fun x y ↦
    (D.level Y n).hom.app ((push R φ f).obj N) ≫
      (res (ordinaryScalarMap R B ψ Y n)).map x ≫ y) h3 h4
  exact hL.trans ((hd N).trans hR.symm)

private def scalarLevelB {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  Scheme.proEtaleRingRestrictionDerivedPullback f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm

-- The ring-change adjunct equation at the counit fixes the single-level mate.
private theorem scalarLevelD_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : DerivedCategory (StrictTower.Modules (R n) X)) :
    (mateEquiv (levelAdj R f n)
      (Scheme.proEtaleRingDerivedAdjunction f (StrictTower.coefficients B Y)
        (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
      (scalarLevelB (R := R) (B := B) (ψ := ψ) f n).inv).app N =
        (scalarLevelD (R := R) (B := B) (ψ := ψ) f n).hom.app N := by
  rw [CategoryTheory.mate_app_eq_adjunct]
  have ht := (Scheme.proEtaleRingSheafChangeAdjunction f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm).2.2
      (((StrictTower.moduleDirectImage (R n) f).rightDerivedFunctor).obj N) N
      ((levelAdj R f n).counit.app N)
  have hh : (levelAdj R f n).homEquiv _ _ ((levelAdj R f n).counit.app N) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id]
    exact (levelAdj R f n).homEquiv _ _ |>.apply_symm_apply (𝟙 _)
  change _ = _ ≫ (scalarLevelD (R := R) (B := B) (ψ := ψ) f n).hom.app N at ht
  change (Scheme.proEtaleRingDerivedAdjunction f (coefficients R Y n)
    (coefficients R X n) (StrictTower.constantRingIso (R n) f)).homEquiv _ _
      ((levelAdj R f n).counit.app N) = 𝟙 _ at hh
  erw [hh, CategoryTheory.Functor.map_id, Category.id_comp] at ht
  exact ht

section LocalizedInverseCube

attribute [local irreducible] Functor.mapDerivedCategoryNatIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarInverseCube_localized {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (hOrd : ∀ M : Modules R φ Y,
      (eqToIso (StrictTower.evaluationPullback B f n)).inv.app ((D.rho Y).obj M) ≫
          ((evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n)).map
            ((D.b f).inv.app M) ≫ (D.level X n).hom.app ((pull R φ f).obj M) =
        (StrictTower.modulePullback B f).map ((D.level Y n).hom.app M) ≫
          (Scheme.proEtaleRingRestrictionPullbackInv f
            (StrictTower.coefficients B Y) (coefficients R Y n)
            (StrictTower.coefficients B X) (coefficients R X n)
            (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
            (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
            (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm).app
              ((eval R φ Y n).obj M) ≫
          (res (ordinaryScalarMap R B ψ X n)).map ((moduleEvalG R φ f n).inv.app M))
    (M : Derived R φ Y) :
    (StrictTower.modulePullback B f).mapDerivedCategory.map
        ((scalarLevel D Y n).inv.app M) ≫
      (StrictTower.evalG B f n).inv.app ((scalarRho D Y).obj M) ≫
      (StrictTower.ev B X n).map ((scalarB D f).inv.app M) =
    (scalarLevelB (R := R) (B := B) (ψ := ψ) f n).inv.app ((ev R φ Y n).obj M) ≫
      (resD (ordinaryScalarMap R B ψ X n)).map ((evalG R φ f n).inv.app M) ≫
      (scalarLevel D X n).inv.app ((G R φ f).obj M) := by
  have := Scheme.proEtaleRingRestrictionPullbackInv_isIso f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm
  let q := asIso (Scheme.proEtaleRingRestrictionPullbackInv f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (Scheme.proEtaleConstantInverseImageMap_naturality f (ψ n)).symm)
  have hc := Functor.mapDerivedCategory_exactCube (D.rho Y)
    ((evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n))
    (StrictTower.modulePullback B f) (eval R φ Y n)
    (res (ordinaryScalarMap R B ψ Y n)) (StrictTower.modulePullback (R n) f)
    (res (ordinaryScalarMap R B ψ X n)) (pull R φ f) (eval R φ X n)
    (StrictTower.towerPullback B f)
    ((evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n)) (D.rho X)
    (D.level Y n) q (moduleEvalG R φ f n).symm
    (eqToIso (StrictTower.evaluationPullback B f n)).symm (D.b f).symm
    (D.level X n) (by
      intro K
      dsimp only [q, asIso_hom]
      exact (hOrd K).symm)
  have ht := congr_app hc M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ht
  have hY : Functor.mapDerivedCategorySquareIso (D.level Y n) = scalarLevel D Y n := rfl
  have hX : Functor.mapDerivedCategorySquareIso (D.level X n) = scalarLevel D X n := rfl
  have hR : (Functor.mapDerivedCategorySquareIso q).hom =
      (scalarLevelB (R := R) (B := B) (ψ := ψ) f n).inv := by
    have hRB : scalarLevelB (R := R) (B := B) (ψ := ψ) f n =
        Functor.mapDerivedCategorySquareIso q.symm := rfl
    rw [hRB]
    exact Functor.square_symm_hom q.symm
  have hG : (Functor.mapDerivedCategorySquareIso (moduleEvalG R φ f n).symm).hom =
      (evalG R φ f n).inv := by
    rw [Functor.square_symm_hom]
    rfl
  have hE : (Functor.mapDerivedCategorySquareIso
      (eqToIso (StrictTower.evaluationPullback B f n)).symm).hom =
      (StrictTower.evalG B f n).inv := by
    rw [Functor.square_symm_hom]
    rfl
  have hB : (Functor.mapDerivedCategorySquareIso (D.b f).symm).hom =
      (scalarB D f).inv := by
    rw [Functor.square_symm_hom]
    rfl
  change (StrictTower.modulePullback B f).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso (D.level Y n)).hom.app M) ≫
    (Functor.mapDerivedCategorySquareIso q).hom.app ((ev R φ Y n).obj M) ≫
    (resD (ordinaryScalarMap R B ψ X n)).map
      ((Functor.mapDerivedCategorySquareIso (moduleEvalG R φ f n).symm).hom.app M) =
    (Functor.mapDerivedCategorySquareIso
      (eqToIso (StrictTower.evaluationPullback B f n)).symm).hom.app
        ((scalarRho D Y).obj M) ≫
    (StrictTower.ev B X n).map
      ((Functor.mapDerivedCategorySquareIso (D.b f).symm).hom.app M) ≫
    (Functor.mapDerivedCategorySquareIso (D.level X n)).hom.app
      ((G R φ f).obj M) at ht
  rw [hY, hX, hR, hG, hE, hB] at ht
  have hz := congrArg (fun z ↦
    (StrictTower.modulePullback B f).mapDerivedCategory.map
      ((scalarLevel D Y n).inv.app M) ≫ z ≫
      (scalarLevel D X n).inv.app ((G R φ f).obj M)) ht
  simp only [Category.assoc] at hz
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app, Category.comp_id] at hz
  erw [Category.assoc] at hz
  exact hz.symm

end LocalizedInverseCube

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarD_evaluation_of_cube
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (hcube : ∀ M : Derived R φ Y,
      (StrictTower.modulePullback B f).mapDerivedCategory.map
          ((scalarLevel D Y n).inv.app M) ≫
        (StrictTower.evalG B f n).inv.app ((scalarRho D Y).obj M) ≫
        (StrictTower.ev B X n).map ((scalarB D f).inv.app M) =
      (scalarLevelB (R := R) (B := B) (ψ := ψ) f n).inv.app ((ev R φ Y n).obj M) ≫
        (resD (ordinaryScalarMap R B ψ X n)).map ((evalG R φ f n).inv.app M) ≫
        (scalarLevel D X n).inv.app ((G R φ f).obj M))
    (N : Derived R φ X) :
    (StrictTower.ev B Y n).map ((scalarD D f).app N) ≫
        (StrictTower.evalR B f n).app ((scalarRho D X).obj N) ≫
        (StrictTower.moduleDirectImage B f).rightDerivedFunctor.map
          ((scalarLevel D X n).hom.app N) =
      (scalarLevel D Y n).hom.app ((P R φ f).obj N) ≫
        (resD (ordinaryScalarMap R B ψ Y n)).map ((evalP R φ f n).hom.app N) ≫
        (scalarLevelD (R := R) (B := B) (ψ := ψ) f n).hom.app
          ((ev R φ X n).obj N) := by
  have ht := CategoryTheory.exchangeMate_cube (adj R φ f) (StrictTower.adj B f)
    (levelAdj R f n)
    (Scheme.proEtaleRingDerivedAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f))
    (ev R φ Y n) (ev R φ X n) (StrictTower.ev B Y n) (StrictTower.ev B X n)
    (evalG R φ f n) (scalarLevel D Y n) (scalarLevel D X n)
    (StrictTower.evalG B f n) (scalarB D f).inv
    (scalarLevelB (R := R) (B := B) (ψ := ψ) f n).inv hcube N
  rw [scalarLevelD_mate] at ht
  unfold StrictTower.moduleDirectImage
  simp only [scalarD, StrictTower.evalR, evalP, evalPMate, TwoSquare.mk,
    Functor.comp_obj,
    Scheme.proEtaleRingDerivedAdjunction, Scheme.proEtaleRingDerivedDirectImage] at ht ⊢
  convert ht using 1
  rfl
/-- Evaluation of the actual mate is the normalized single-level comparison, through
exactly the recorded localization and direct-image evaluation identifications.
Source: Stacks 07A6, 0D6D, 0D6E; Zheng 4.10
(blueprint: lem-sf-semilinear-scalar-derived-comparison).
Proof: localize D.level and D.b termwise, using localization uniqueness. The evaluation
comparisons evalP and StrictTower.evalR are the mates of inverse-image evaluation.
The evaluation-of-transposes formula of semilinearDerivedSections therefore identifies
the evaluated scalarD word with the single-level unit--inverse-b--counit word. Apply
proEtaleRingSheafChangeAdjunction to t equal to the C_n counit. Its transpose is the
identity by the triangle identity, so that word is precisely scalarLevelD. Naturality
moves the evaluation identifications to the displayed positions. This is an equality
of constructed words, not an argument from faithfulness of evaluation. -/
theorem scalarD_evaluation (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (N : Derived R φ X) :
    (StrictTower.ev B Y n).map ((scalarD D f).app N) ≫
        (StrictTower.evalR B f n).app ((scalarRho D X).obj N) ≫
        (StrictTower.moduleDirectImage B f).rightDerivedFunctor.map
          ((scalarLevel D X n).hom.app N) =
      (scalarLevel D Y n).hom.app ((P R φ f).obj N) ≫
        (resD.{u + 1, u, u + 1} (ordinaryScalarMap R B ψ Y n)).map
          ((evalP R φ f n).hom.app N) ≫
        (scalarLevelD (R := R) (B := B) (ψ := ψ) f n).hom.app
          ((ev R φ X n).obj N) := by
  have _hcompat := hψ
  clear hψ _hcompat
  exact scalarD_evaluation_of_cube D f n
    (scalarInverseCube_localized D f n
      (scalarOrdinaryInverseCube D f n (scalarDOrd_evaluation D f n))) N

-- Homology detects isomorphisms, and tower homology is computed componentwise.
private theorem scalarD_isIso (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (scalarD D f) := by
  have hc (N : Derived R φ X) : IsIso ((scalarD D f).app N) := by
    have heval (n : ℕ) :
        IsIso ((StrictTower.ev B Y n).map ((scalarD D f).app N)) := by
      have := StrictTower.evalR_isIso B f n
      have h := scalarD_evaluation D hψ f n N
      have : IsIso ((StrictTower.ev B Y n).map ((scalarD D f).app N) ≫
          (StrictTower.evalR B f n).app ((scalarRho D X).obj N) ≫
          (StrictTower.moduleDirectImage B f).rightDerivedFunctor.map
            ((scalarLevel D X n).hom.app N)) := by
        rw [h]
        infer_instance
      exact IsIso.of_isIso_comp_right
        ((StrictTower.ev B Y n).map ((scalarD D f).app N))
        ((StrictTower.evalR B f n).app ((scalarRho D X).obj N) ≫
          (StrictTower.moduleDirectImage B f).rightDerivedFunctor.map
            ((scalarLevel D X n).hom.app N))
    apply (DerivedCategory.isIso_iff _ _).2
    intro q
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro n
    have := heval n.unop
    exact (NatIso.isIso_map_iff
      (((evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj n).mapDerivedCategoryHomologyFunctorIso q)
      ((scalarD D f).app N)).2 (by
        change IsIso ((DerivedCategory.homologyFunctor (StrictTower.Modules B Y) q).map
          ((StrictTower.ev B Y n.unop).map ((scalarD D f).app N)))
        infer_instance)
  exact NatIso.isIso_of_isIso_app _

section OrdinaryAlpha
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] StrictTower.modulePullback Functor.leftAdjoint

attribute [local instance] StrictTower.clopenTowerAbelian
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors StrictTower.alpha

private theorem localized_of_descent
    {A C E F : Type*} [Category A] [Category C] [Category E] [Category F]
    [Abelian A] [Abelian C] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory C] [HasDerivedCategory E]
    [HasDerivedCategory F]
    (f : A ⥤ C) (g : C ⥤ F) (h : A ⥤ E) (k : E ⥤ F)
    [f.Additive] [g.Additive] [h.Additive] [k.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    [PreservesFiniteLimits h] [PreservesFiniteColimits h]
    [PreservesFiniteLimits k] [PreservesFiniteColimits k]
    (t : f ⋙ g ⟶ h ⋙ k)
    (d : f.mapDerivedCategory ⋙ g.mapDerivedCategory ⟶
      h.mapDerivedCategory ⋙ k.mapDerivedCategory)
    (ht : StrictTower.ClopenProjectorDescent (f ⋙ g) (h ⋙ k) t
      ((Functor.mapDerivedCategoryCompIso f g).inv ≫ d ≫
        (Functor.mapDerivedCategoryCompIso h k).hom)) : localizedArrow f g h k t = d := by
  have he : Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) _ _
      (f ⋙ g).mapDerivedCategory (h ⋙ k).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q) =
      (Functor.mapDerivedCategoryCompIso f g).inv ≫ d ≫
        (Functor.mapDerivedCategoryCompIso h k).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    apply (cancel_mono ((h ⋙ k).mapDerivedCategoryFactors.hom.app K)).mp
    rw [ht K]
    simp only [Localization.liftNatTrans_app, Functor.whiskerRight_app, Category.assoc,
      Localization.Lifting.iso, Iso.inv_hom_id_app, Category.comp_id]
  unfold localizedArrow
  rw [he]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem scalarTowerAlpha_localized {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    localizedArrow (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
      (StrictTower.towerPullback B r) (StrictTower.towerJ B k)
      (D.alpha k r p i h) = StrictTower.alpha B k r p i h := by
  rw [scalarOrdinaryAlphaNormalization D]
  exact localized_of_descent _ _ _ _ _ _
    (StrictTower.alpha_eq_localized_singleAlpha B k r p i h)

end OrdinaryAlpha

section OpenMate
attribute [local instance] StrictTower.clopenTowerAbelian

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem leftMateOfUnitTwo
    {C E : Type*} [Category C] [Category E] {L : C ⥤ E} {F : E ⥤ C}
    (a : L ⊣ F) {X Y : C} {Z : E} (f : L.obj X ⟶ Z) (g : X ⟶ Y)
    (h : Y ⟶ F.obj Z) (he : a.unit.app X ≫ F.map f = g ≫ h) :
    f = L.map g ≫ L.map h ≫ a.counit.app Z := by
  have ht := (a.homEquiv X Z).symm_apply_apply f
  rw [Adjunction.homEquiv_unit, he, Adjunction.homEquiv_counit, Functor.map_comp] at ht
  exact ht.symm.trans (Category.assoc _ _ _)

private theorem exactLeftMate
    {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁)
  {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂} (adj₂ : f₂ ⊣ g₂)
  {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (a : f₁ ⋙ v ≅ u ⋙ f₂)
  (d₁ : f₁.mapDerivedCategory ⊣ g₁.mapDerivedCategory)
  (d₂ : f₂.mapDerivedCategory ⊣ g₂.mapDerivedCategory)
  (hu₁ : ∀ X : HomotopyCategory C₁ (.up ℤ),
    d₁.unit.app (DerivedCategory.Qh.obj X) ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        g₁.mapDerivedCategoryFactorsh.hom.app ((f₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X))
  (hu₂ : ∀ X : HomotopyCategory C₂ (.up ℤ),
    d₂.unit.app (DerivedCategory.Qh.obj X) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.hom.app X) ≫
        g₂.mapDerivedCategoryFactorsh.hom.app ((f₂.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X))
    (ha : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (a.inv.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K)) (M : DerivedCategory C₁) :
    (Functor.mapDerivedCategorySquareIso a).inv.app M =
      f₂.mapDerivedCategory.map (u.mapDerivedCategory.map (d₁.unit.app M)) ≫
        f₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj M)) ≫ d₂.counit.app
            (v.mapDerivedCategory.obj (f₁.mapDerivedCategory.obj M)) := by
  have hd := StrictTower.exact_mate adj₁ adj₂ τ a.symm d₁ d₂ hu₁ hu₂ ha M
  rw [Functor.square_symm_hom] at hd
  exact leftMateOfUnitTwo d₂ _ _ _ hd

private theorem scalarOpenAdj_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : StrictTower.exactAdj (moduleJAdj R φ j) = jAdj R φ j := by
  unfold StrictTower.exactAdj jAdj
  rfl

attribute [local irreducible] StrictTower.jAdj jAdj
  scalarA scalarB Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarA_leftMate {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : Derived R φ U) :
    (scalarA D j).inv.app M =
      (StrictTower.J B j).map ((scalarRho D U).map ((jAdj R φ j).unit.app M)) ≫
        (StrictTower.J B j).map ((scalarB D j).hom.app ((J R φ j).obj M)) ≫
        (StrictTower.jAdj B j).counit.app ((scalarRho D X).obj ((J R φ j).obj M)) := by
  have hOrd (K : Modules R φ U) :
      (scalarTowerOpenAdj B j).unit.app ((D.rho U).obj K) ≫
        (StrictTower.towerPullback B j).map ((D.a j).inv.app K) =
      (D.rho U).map ((moduleJAdj R φ j).unit.app K) ≫
        (D.b j).hom.app ((extension R φ j).obj K) := by
    apply (cancel_mono ((StrictTower.towerPullback B j).map ((D.a j).hom.app K))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact (D.open_unit j K).symm
  have ht := exactLeftMate (moduleJAdj R φ j) (scalarTowerOpenAdj B j)
    (D.b j) (D.a j) (StrictTower.exactAdj (moduleJAdj R φ j))
    (StrictTower.exactAdj (scalarTowerOpenAdj B j))
    (StrictTower.exactAdj_unit _) (StrictTower.exactAdj_unit _) hOrd M
  rw [scalarOpenAdj_eq] at ht
  unfold scalarTowerOpenAdj at ht
  rw [StrictTower.exactAdj_jAdj] at ht
  unfold scalarA scalarB
  set_option backward.isDefEq.respectTransparency false in
    exact ht

end OpenMate

attribute [local irreducible] scalarA scalarB
  Functor.mapDerivedCategoryNatIso
  localizedArrow alpha StrictTower.alpha Functor.mapDerivedCategory

private theorem scalarA_eq {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Functor.mapDerivedCategorySquareIso (D.a j) = scalarA D j := by
  unfold scalarA
  rfl
private theorem scalarB_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.mapDerivedCategorySquareIso (D.b f) = scalarB D f := by
  unfold scalarB
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem localize_scalar_cube
    (C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type v)
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Category.{w} C₄] [Category.{w} C₅] [Category.{w} C₆] [Category.{w} C₇]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [Abelian C₄] [Abelian C₅] [Abelian C₆] [Abelian C₇]
    [HasDerivedCategory.{x} C₀] [HasDerivedCategory.{x} C₁]
    [HasDerivedCategory.{x} C₂] [HasDerivedCategory.{x} C₃]
    [HasDerivedCategory.{x} C₄] [HasDerivedCategory.{x} C₅]
    [HasDerivedCategory.{x} C₆] [HasDerivedCategory.{x} C₇]
    (If : C₀ ⥤ C₁) [If.Additive]
    [PreservesFiniteLimits If] [PreservesFiniteColimits If]
    (Pf : C₁ ⥤ C₂) [Pf.Additive]
    [PreservesFiniteLimits Pf] [PreservesFiniteColimits Pf]
    (Kf : C₃ ⥤ C₂) [Kf.Additive]
    [PreservesFiniteLimits Kf] [PreservesFiniteColimits Kf]
    (Qf : C₀ ⥤ C₃) [Qf.Additive]
    [PreservesFiniteLimits Qf] [PreservesFiniteColimits Qf]
    (I₁f : C₄ ⥤ C₅) [I₁f.Additive]
    [PreservesFiniteLimits I₁f] [PreservesFiniteColimits I₁f]
    (P₁f : C₅ ⥤ C₆) [P₁f.Additive]
    [PreservesFiniteLimits P₁f] [PreservesFiniteColimits P₁f]
    (K₁f : C₇ ⥤ C₆) [K₁f.Additive]
    [PreservesFiniteLimits K₁f] [PreservesFiniteColimits K₁f]
    (Q₁f : C₄ ⥤ C₇) [Q₁f.Additive]
    [PreservesFiniteLimits Q₁f] [PreservesFiniteColimits Q₁f]
    (Af : C₂ ⥤ C₆) [Af.Additive]
    [PreservesFiniteLimits Af] [PreservesFiniteColimits Af]
    (Hf : C₁ ⥤ C₅) [Hf.Additive]
    [PreservesFiniteLimits Hf] [PreservesFiniteColimits Hf]
    (C₀f : C₀ ⥤ C₄) [C₀f.Additive]
    [PreservesFiniteLimits C₀f] [PreservesFiniteColimits C₀f]
    (Df : C₃ ⥤ C₇) [Df.Additive]
    [PreservesFiniteLimits Df] [PreservesFiniteColimits Df]
    (al0 : If ⋙ Pf ⟶ Qf ⋙ Kf) (al₁0 : I₁f ⋙ P₁f ⟶ Q₁f ⋙ K₁f)
    (bi0 : If ⋙ Hf ≅ C₀f ⋙ I₁f) (bk0 : Kf ⋙ Af ≅ Df ⋙ K₁f)
    (gp0 : Pf ⋙ Af ≅ Hf ⋙ P₁f) (gr0 : Qf ⋙ Df ≅ C₀f ⋙ Q₁f)
    (hOrd : ∀ N : C₀,
      Af.map (al0.app N) ≫ bk0.hom.app (Qf.obj N) ≫ K₁f.map (gr0.hom.app N) =
      gp0.hom.app (If.obj N) ≫ P₁f.map (bi0.hom.app N) ≫ al₁0.app (C₀f.obj N))
    (ai : If.mapDerivedCategory ⋙ Hf.mapDerivedCategory ≅
      C₀f.mapDerivedCategory ⋙ I₁f.mapDerivedCategory)
    (ak : Kf.mapDerivedCategory ⋙ Af.mapDerivedCategory ≅
      Df.mapDerivedCategory ⋙ K₁f.mapDerivedCategory)
    (bp : Pf.mapDerivedCategory ⋙ Af.mapDerivedCategory ≅
      Hf.mapDerivedCategory ⋙ P₁f.mapDerivedCategory)
    (br : Qf.mapDerivedCategory ⋙ Df.mapDerivedCategory ≅
      C₀f.mapDerivedCategory ⋙ Q₁f.mapDerivedCategory)
    (hai : (Functor.mapDerivedCategoryCompIso If Hf ≪≫
      Functor.mapDerivedCategoryNatIso bi0 ≪≫
      (Functor.mapDerivedCategoryCompIso C₀f I₁f).symm) = ai)
    (hak : (Functor.mapDerivedCategoryCompIso Kf Af ≪≫
      Functor.mapDerivedCategoryNatIso bk0 ≪≫ (Functor.mapDerivedCategoryCompIso Df K₁f).symm) = ak)
    (hbp : (Functor.mapDerivedCategoryCompIso Pf Af ≪≫
      Functor.mapDerivedCategoryNatIso gp0 ≪≫ (Functor.mapDerivedCategoryCompIso Hf P₁f).symm) = bp)
    (hbr : (Functor.mapDerivedCategoryCompIso Qf Df ≪≫
      Functor.mapDerivedCategoryNatIso gr0 ≪≫
      (Functor.mapDerivedCategoryCompIso C₀f Q₁f).symm) = br)
    (d0 : If.mapDerivedCategory ⋙ Pf.mapDerivedCategory ⟶
      Qf.mapDerivedCategory ⋙ Kf.mapDerivedCategory)
    (d1 : I₁f.mapDerivedCategory ⋙ P₁f.mapDerivedCategory ⟶
      Q₁f.mapDerivedCategory ⋙ K₁f.mapDerivedCategory)
    (hd0 : localizedArrow If Pf Qf Kf al0 = d0)
    (hd1 : localizedArrow I₁f P₁f Q₁f K₁f al₁0 = d1)
    (M : DerivedCategory C₀) :
    Af.mapDerivedCategory.map (d0.app M) ≫
      ak.hom.app (Qf.mapDerivedCategory.obj M) ≫
      K₁f.mapDerivedCategory.map (br.hom.app M) =
    bp.hom.app (If.mapDerivedCategory.obj M) ≫
      P₁f.mapDerivedCategory.map (ai.hom.app M) ≫
      d1.app (C₀f.mapDerivedCategory.obj M) := by
  have ho (N : C₀) : P₁f.map (bi0.hom.app N) ≫ al₁0.app (C₀f.obj N) =
      gp0.inv.app (If.obj N) ≫ Af.map (al0.app N) ≫ bk0.hom.app (Qf.obj N) ≫
        K₁f.map (gr0.hom.app N) := by
    rw [hOrd N, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have ht := localize_cube_functors C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇
    If Pf Kf Qf I₁f P₁f K₁f Q₁f Af Hf C₀f Df
    al0 al₁0 bi0.hom bk0.hom gp0.inv gr0.hom ho M
  rw [localizedArrow_iso_hom, localizedArrow_iso_hom,
    localizedArrow_iso_inv, localizedArrow_iso_hom] at ht
  rw [hd0, hd1, hai, hak, hbp, hbr] at ht
  have hh := congrArg
    (fun t ↦ bp.hom.app
      (If.mapDerivedCategory.obj M) ≫ t) ht
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh.symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in

private theorem scalarAlphaComparison {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : Derived R φ S)
    (hAlpha : localizedArrow (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
      (StrictTower.towerPullback B r) (StrictTower.towerJ B k)
      (D.alpha k r p i h) = StrictTower.alpha B k r p i h) :
    (scalarRho D W).map ((alpha R φ k r p i h).app M) ≫
      (scalarA D k).hom.app ((G R φ r).obj M) ≫
      (StrictTower.J B k).map ((scalarB D r).hom.app M) =
    (scalarB D p).hom.app ((J R φ i).obj M) ≫
      (StrictTower.G B p).map ((scalarA D i).hom.app M) ≫
      (StrictTower.alpha B k r p i h).app ((scalarRho D S).obj M) := by
  have ht := localize_scalar_cube
    (Modules R φ S) (Modules R φ T) (Modules R φ W) (Modules R φ V)
    (StrictTower.Towers B S) (StrictTower.Towers B T)
    (StrictTower.Towers B W) (StrictTower.Towers B V)
    (extension R φ i) (pull R φ p) (extension R φ k) (pull R φ r)
    (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerJ B k) (StrictTower.towerPullback B r)
    (D.rho W) (D.rho T) (D.rho S) (D.rho V)
    (moduleAlpha R φ k r p i h) (D.alpha k r p i h)
    (D.a i) (D.a k) (D.b p) (D.b r) (D.alpha_comparison k r p i h)
    (scalarA D i) (scalarA D k) (scalarB D p) (scalarB D r)
    (scalarA_eq D i) (scalarA_eq D k) (scalarB_eq D p) (scalarB_eq D r)
    (alpha R φ k r p i h) _ (alpha_localized R φ k r p i h).symm rfl M
  exact ht.trans (congrArg
    (fun t ↦ (scalarB D p).hom.app ((J R φ i).obj M) ≫
      (StrictTower.G B p).map ((scalarA D i).hom.app M) ≫
      t.app ((scalarRho D S).obj M)) hAlpha)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Derived scalar comparisons are invertible specified mates and preserve intrinsic
alpha before proper mating, for every commutative proper/quasi-compact-open square.
Source: Stacks 03D7, 07A6, 04VG; blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-derived-comparison).
Proof: (1) localize D.b and its inverse; localization respects both inverse identities.
The definition scalarD is the specified adjunction mate of scalarB.inv. (2) By
scalarD_evaluation its evaluations are the normalized invertible single-level ring-change
comparisons. Joint detection of isomorphisms in semilinearDerivedSections, specialized
to the constant B system (the strict-tower category), proves every component invertible.
Their inverses are natural by the naturality squares, giving IsIso of scalarD.
(3) Localize D.a and its inverse. The ordinary open-unit normalization says that D.a.inv
is the left mate of D.b. Cancel unit and counit using the triangle identity and descend
this equality with the canonical derived open adjunctions; this gives the displayed
left-mate word. (4) D.alpha_comparison is an equality of ordinary system maps built
from cartesian beta, the clopen projector and normalized compositors. Localize the
whole equality. The varying-ring alpha is its specified localization, and the tower
alpha is the same localized beta/projector/compositor word. Functoriality of localization
gives the final equality on systems, including noncartesian squares. No equality is
inferred from levelwise evaluation, and no proper mate has yet been taken. -/
theorem derivedScalarComparison (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n) :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (scalarD D f)) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : Derived R φ U),
      (scalarA D j).inv.app M =
        (StrictTower.J B j).map ((scalarRho D U).map ((jAdj R φ j).unit.app M)) ≫
          (StrictTower.J B j).map ((scalarB D j).hom.app ((J R φ j).obj M)) ≫
          (StrictTower.jAdj B j).counit.app ((scalarRho D X).obj ((J R φ j).obj M))) ∧
    (∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
      (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
      [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
      (M : Derived R φ S),
      (scalarRho D W).map ((alpha R φ k r p i h).app M) ≫
          (scalarA D k).hom.app ((G R φ r).obj M) ≫
          (StrictTower.J B k).map ((scalarB D r).hom.app M) =
        (scalarB D p).hom.app ((J R φ i).obj M) ≫
          (StrictTower.G B p).map ((scalarA D i).hom.app M) ≫
          (StrictTower.alpha B k r p i h).app ((scalarRho D S).obj M)) := by
  refine ⟨fun f ↦ scalarD_isIso D hψ f, ?_, ?_⟩
  · intro U X j _ M
    exact scalarA_leftMate D j M
  · intro V W S T k r p i _ _ _ _ _ _ h M
    exact scalarAlphaComparison D k r p i h M (scalarTowerAlpha_localized D k r p i h)

end AlgebraicGeometry.ProEtale.VaryingRing
