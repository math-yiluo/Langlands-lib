/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarOrdinaryInterface
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Exact levelwise scalar restriction

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03D7 and 03DI
(blueprint: lem-sf-semilinear-scalar-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- The exact restriction functor and its identity-on-sections level identifications.
Source: Stacks 03CT, 03CZ and 03DA
(blueprint: lem-sf-semilinear-scalar-restriction). -/
structure OrdinaryScalarRestriction where
  /-- Restriction from actual semilinear systems to actual strict B towers. -/
  rho : ∀ X : Scheme.{u}, Modules R φ X ⥤ StrictTower.Towers B X
  /-- Additivity on the unchanged underlying maps. -/
  additive : ∀ X : Scheme.{u}, (rho X).Additive
  /-- Left exactness. -/
  limits : ∀ X : Scheme.{u}, PreservesFiniteLimits (rho X)
  /-- Right exactness, including nonflat scalar maps. -/
  colimits : ∀ X : Scheme.{u}, PreservesFiniteColimits (rho X)
  /-- Each level is the existing restriction-of-scalars functor. -/
  level : ∀ (X : Scheme.{u}) (n : ℕ),
    rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) ≅
      eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n)
  /-- Identification is identity on sections. -/
  level_sections : ∀ (X : Scheme.{u}) (n : ℕ) (M : Modules R φ X) (H : X.ProEtᵒᵖ),
    ∀ x : (((rho X).obj M).obj (op n)).val.obj H,
      HEq (((level X n).hom.app M).val.app H x) x
  /-- Under the level identification all transitions are the original section restrictions. -/
  transitions : ∀ (X : Scheme.{u}) (M : Modules R φ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((rho X).obj M).obj (op (n + 1))).val.obj H),
    ((level X n).hom.app M).val.app H
        ((((rho X).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H x) =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op
        (((level X (n + 1)).hom.app M).val.app H x)

private def scalarComposeIso {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) {A S T : Sheaf J CommRingCat.{r}}
    (a : A ⟶ S) (b : S ⟶ T) (c : A ⟶ T) (h : c = a ≫ b) :
    res b ⋙ res a ≅ res c :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun H ↦
      (ModuleCat.restrictScalarsComp'App (a.hom.app H).hom (b.hom.app H).hom
        (c.hom.app H).hom (congrArg (fun q ↦ (q.hom.app H).hom) h)
        (M.val.obj H)).symm) (by intros; ext x; rfl)))
    (by intros; ext H x; rfl)

private theorem scalarComposeIso_sections {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
    {A S T : Sheaf J CommRingCat.{r}} (a : A ⟶ S) (b : S ⟶ T) (d : A ⟶ T)
    (h : d = a ≫ b) (M : WeilConjectures.SemilinearSections.Mod.{c, v, r} J T)
    (H : Cᵒᵖ) (x : M.val.obj H) :
    (((scalarComposeIso J a b d h).hom.app M).val.app H) x = x := rfl

attribute [local irreducible] scalarComposeIso

section SequenceRestriction

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (S : ℕ → Sheaf J CommRingCat.{r})
  (τ : ∀ n, S (n + 1) ⟶ S n) (A : Sheaf J CommRingCat.{r})
  (a : ∀ n, A ⟶ S n) (ha : ∀ n, a (n + 1) ≫ τ n = a n)

private def scalarResComp (n : ℕ) :
    res (coefficientMap J S τ (Nat.le_succ n)) ⋙ res (a (n + 1)) ≅ res (a n) :=
  scalarComposeIso J _ _ _ (by
    simp only [coefficientMap, rings, Functor.ofOpSequence_map_homOfLE_succ, ha])

set_option backward.isDefEq.respectTransparency false in
private theorem scalarResComp_sections (n : ℕ)
    (M : WeilConjectures.SemilinearSections.Mod.{c, v, r} J (S n))
    (H : Cᵒᵖ) (x : M.val.obj H) :
    ((scalarResComp J S τ A a ha n).hom.app M).val.app H x = x := by
  unfold scalarResComp
  exact scalarComposeIso_sections _ _ _ _ _ M H x

attribute [local irreducible] scalarResComp

private abbrev scalarLevel (n : ℕ) :=
  WeilConjectures.SemilinearSections.evaluation.{c, v, r} J S τ n ⋙ res (a n)

private def scalarTransition (n : ℕ) :
    scalarLevel J S τ A a (n + 1) ⟶ scalarLevel J S τ A a n where
  app M := (res (a (n + 1))).map ((transition J S τ (Nat.le_succ n)).app M) ≫
    (scalarResComp J S τ A a ha n).hom.app
      ((WeilConjectures.SemilinearSections.evaluation J S τ n).obj M)
  naturality {M N} f := by
    have ht := (transition J S τ (Nat.le_succ n)).naturality f
    have hc := (scalarResComp J S τ A a ha n).hom.naturality
      ((WeilConjectures.SemilinearSections.evaluation J S τ n).map f)
    dsimp only [Functor.comp_map] at ht hc
    dsimp only [scalarLevel, Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, ht, Functor.map_comp, Category.assoc, hc]
    rfl

private theorem scalarStep_sections (M : Systems.{c, v, r} J S τ) (n : ℕ) (H : Cᵒᵖ)
    (x : M.val.obj (op (n + 1, H.unop))) :
    ((scalarTransition J S τ A a ha n).app M).val.app H x =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op x := by
  have hs := scalarResComp_sections J S τ A a ha n
    ((WeilConjectures.SemilinearSections.evaluation J S τ n).obj M) H
    (((transition J S τ (Nat.le_succ n)).app M).val.app H x)
  have ht := congrFun
    (eq_of_heq ((transition_exists J S τ (Nat.le_succ n)).exists.choose_spec M H)) x
  exact hs.trans ht

attribute [local irreducible] scalarTransition

private def scalarRho : Systems.{c, v, r} J S τ ⥤
    ℕᵒᵖ ⥤ WeilConjectures.SemilinearSections.Mod.{c, v, r} J A :=
  (Functor.ofOpSequence (scalarTransition J S τ A a ha)).flip

private def scalarLevelIso (n : ℕ) :
    scalarRho J S τ A a ha ⋙
      (evaluation ℕᵒᵖ (WeilConjectures.SemilinearSections.Mod.{c, v, r} J A)).obj (op n) ≅
        scalarLevel J S τ A a n :=
  Iso.refl _

private theorem scalarRho_additive : (scalarRho J S τ A a ha).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  exact (scalarLevel J S τ A a n.unop).map_add (f := f) (g := g)

private theorem scalarLevelIso_sections (n : ℕ) (M : Systems.{c, v, r} J S τ)
    (H : Cᵒᵖ) (x : M.val.obj (op (n, H.unop))) :
    HEq (((scalarLevelIso J S τ A a ha n).hom.app M).val.app H x) x := HEq.rfl

private theorem scalarRho_transitions (M : Systems.{c, v, r} J S τ) (n : ℕ) (H : Cᵒᵖ)
    (x : M.val.obj (op (n + 1, H.unop))) :
    ((scalarLevelIso J S τ A a ha n).hom.app M).val.app H
        ((((scalarRho J S τ A a ha).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H x) =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op
        (((scalarLevelIso J S τ A a ha (n + 1)).hom.app M).val.app H x) := by
  change (((Functor.ofOpSequence (scalarTransition J S τ A a ha)).map
    (homOfLE (Nat.le_succ n)).op).app M).val.app H x = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  exact scalarStep_sections J S τ A a ha M n H x

attribute [local irreducible] scalarRho scalarLevelIso

private theorem scalarRho_limits : PreservesFiniteLimits (scalarRho J S τ A a ha) := by
  apply preservesFiniteLimits_of_evaluation
  intro n
  have := evaluationLimits.{c, v, r} J S τ n.unop
  have := resLimits.{c, v, r} (a n.unop)
  have : PreservesFiniteLimits (scalarLevel J S τ A a n.unop) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (scalarLevelIso J S τ A a ha n.unop).symm

private theorem scalarRho_colimits : PreservesFiniteColimits (scalarRho J S τ A a ha) := by
  apply preservesFiniteColimits_of_evaluation
  intro n
  have := evaluationColimits.{c, v, r} J S τ n.unop
  have := resColimits.{c, v, r} (a n.unop)
  have : PreservesFiniteColimits (scalarLevel J S τ A a n.unop) :=
    comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (scalarLevelIso J S τ A a ha n.unop).symm

end SequenceRestriction

/-- Restrict each coefficient action and retain all section maps.
Source: Stacks 03CT, 03CZ and 03DA
(blueprint: lem-sf-semilinear-scalar-restriction).
Proof: compose each level evaluation with restriction along the constant-sheaf map.
The equality psi_(n+1) phi_n = psi_n identifies the twice-restricted coefficient
module with the directly restricted one. Compose that identification with the system
transition. These natural transformations define a tower-valued functor. Its maps
are the original section maps, so it is additive. Each evaluation and scalar
restriction preserves finite limits and colimits. Evaluation detects these properties
in the tower category, proving exactness. The level identifications and transition
formula are the identity section prescriptions of the construction. -/
theorem ordinaryScalarRestriction (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n) :
    Nonempty (OrdinaryScalarRestriction R φ B ψ) := by
  have ha (X : Scheme.{u}) (n : ℕ) :
      ordinaryScalarMap R B ψ X (n + 1) ≫ coefficientTransition R φ X n =
        ordinaryScalarMap R B ψ X n := by
    simp only [ordinaryScalarMap, coefficientTransition, ← Functor.map_comp, hψ]
  let ρ (X : Scheme.{u}) := scalarRho (Scheme.ProEt.topology X) (coefficients R X)
    (coefficientTransition R φ X) (StrictTower.coefficients B X)
    (ordinaryScalarMap R B ψ X) (ha X)
  refine ⟨{
    rho := ρ
    additive := fun X ↦ scalarRho_additive _ _ _ _ _ (ha X)
    limits := fun X ↦ scalarRho_limits _ _ _ _ _ (ha X)
    colimits := fun X ↦ scalarRho_colimits _ _ _ _ _ (ha X)
    level := fun X n ↦ scalarLevelIso _ _ _ _ _ (ha X) n
    level_sections := fun X n M H ↦ scalarLevelIso_sections _ _ _ _ _ (ha X) n M H
    transitions := fun X M n H x ↦ scalarRho_transitions _ _ _ _ _ (ha X) M n H x }⟩

end AlgebraicGeometry.ProEtale.VaryingRing
