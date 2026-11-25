/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Ordinary coefficient evaluation of the clopen comparison

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09AE and 0F7B.
The evaluation used here first takes an ordinary system component, then makes a
constant tower concentrated in degree zero. Its faithfulness concerns ordinary
system morphisms only (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

/-- The realization functor is fixed uniquely by its explicit construction.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons).
Proof: the displayed functor is a witness; the defining equality gives uniqueness. -/
theorem ordinaryRealization_existsUnique (n : ℕ) (X : Scheme.{u}) :
    ∃! E : Modules R φ X ⥤ StrictTower.Derived (R n) X,
      E = eval R φ X n ⋙ Functor.const ℕᵒᵖ ⋙
        DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0 := by
  exact ⟨_, rfl, fun _ h ↦ h⟩

/-- An actual ordinary component, viewed as a degree-zero constant strict tower.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def ordinaryRealization (n : ℕ) (X : Scheme.{u}) :
    Modules R φ X ⥤ StrictTower.Derived (R n) X :=
  (ordinaryRealization_existsUnique R φ n X).choose

/-- The realization retains exactly the explicit component/single construction.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons).
Proof: this is the equality in its proved unique specification. -/
theorem ordinaryRealization_eq (n : ℕ) (X : Scheme.{u}) :
    ordinaryRealization R φ n X = eval R φ X n ⋙ Functor.const ℕᵒᵖ ⋙
      DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0 :=
  (ordinaryRealization_existsUnique R φ n X).choose_spec.1

attribute [local irreducible] ordinaryRealization moduleAlpha moduleGComp moduleJComp
  StrictTower.alpha StrictTower.G StrictTower.J StrictTower.gComp StrictTower.jComp
  Functor.leftAdjoint

/-- A square comparison records its four functors before its component equation.
Source: functoriality of the clopen comparison, Zheng 4.1
(blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
structure OrdinarySquareComparison
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {R₀ : C ⥤ A} {P₀ : D ⥤ B} {K : A ⥤ B} {I : C ⥤ D}
    {r : C' ⥤ A'} {p : D' ⥤ B'} {k : A' ⥤ B'} {i : C' ⥤ D'}
    (eR : R₀ ⋙ EA ≅ EC ⋙ r) (eP : P₀ ⋙ EB ≅ ED ⋙ p)
    (eK : K ⋙ EB ≅ EA ⋙ k) (eI : I ⋙ ED ≅ EC ⋙ i)
    (a : I ⋙ P₀ ⟶ R₀ ⋙ K) (a' : i ⋙ p ⟶ r ⋙ k) : Prop where
  equation (N : C) : EB.map (a.app N) ≫ eK.hom.app (R₀.obj N) ≫
      k.map (eR.hom.app N) =
    eP.hom.app (I.obj N) ≫ p.map (eI.hom.app N) ≫ a'.app (EC.obj N)

/-- The inverse-image comparisons for ordinary realization.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
abbrev OrdinaryPullComparison (n : ℕ) :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    pull R φ f ⋙ ordinaryRealization R φ n X ≅
      ordinaryRealization R φ n Y ⋙ StrictTower.G (R n) f

/-- The open-extension comparisons for ordinary realization.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
abbrev OrdinaryOpenComparison (n : ℕ) :=
  ∀ (U X : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j],
    extension R φ j ⋙ ordinaryRealization R φ n X ≅
      ordinaryRealization R φ n U ⋙ StrictTower.J (R n) j

/-- Pullback compositor normalization.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def OrdinaryPullComposition (n : ℕ) (gIso : OrdinaryPullComparison R φ n) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules R φ Z),
    (ordinaryRealization R φ n X).map ((moduleGComp R φ f g).hom.app N) ≫
        (gIso _ _ f).hom.app ((pull R φ g).obj N) ≫
        (StrictTower.G (R n) f).map ((gIso _ _ g).hom.app N) =
      (gIso _ _ (f ≫ g)).hom.app N ≫
        (StrictTower.gComp (R n) f g).hom.app ((ordinaryRealization R φ n Z).obj N)

/-- Extension compositor normalization.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def OrdinaryOpenComposition (n : ℕ) (jIso : OrdinaryOpenComparison R φ n) : Prop :=
  ∀ {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (N : Modules R φ U),
    (ordinaryRealization R φ n X).map ((moduleJComp R φ i j).hom.app N) ≫
        (jIso _ _ (i ≫ j)).hom.app N =
      (jIso _ _ j).hom.app ((extension R φ i).obj N) ≫
        (StrictTower.J (R n) j).map ((jIso _ _ i).hom.app N) ≫
        (StrictTower.jComp (R n) i j).hom.app ((ordinaryRealization R φ n U).obj N)

/-- Preservation of the single-square clopen arrow.
Source: Stacks 0F7B (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def OrdinaryClopenComparison (n : ℕ) (gIso : OrdinaryPullComparison R φ n)
    (jIso : OrdinaryOpenComparison R φ n) : Prop :=
  ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i),
    OrdinarySquareComparison
      (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n W)
      (EC := ordinaryRealization R φ n S) (ED := ordinaryRealization R φ n T)
      (R₀ := pull R φ r) (P₀ := pull R φ p)
      (K := extension R φ k) (I := extension R φ i)
      (r := StrictTower.G (R n) r) (p := StrictTower.G (R n) p)
      (k := StrictTower.J (R n) k) (i := StrictTower.J (R n) i)
      (gIso _ _ r) (gIso _ _ p) (jIso _ _ k) (jIso _ _ i)
      (moduleAlpha R φ k r p i h) (StrictTower.alpha (R n) k r p i h)

section ConstantSingle

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)]

/-- Constant towers and the degree-zero embedding commute with exact functors.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def ordinaryConstantSingleComparison :
    F ⋙ (Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0) ≅
      (Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0) ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso ℕᵒᵖ F) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategorySingleFunctor 0).symm ≪≫
    (Functor.associator _ _ _).symm

end ConstantSingle

/-- The actual inverse-image comparison, obtained from moduleEvalG and degree zero.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def ordinaryPullComparison (n : ℕ) : OrdinaryPullComparison R φ n := by
  intro X Y f
  unfold StrictTower.G
  let C := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0
  let D := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) Y) 0
  let eX := eqToIso (ordinaryRealization_eq R φ n X)
  let eY := eqToIso (ordinaryRealization_eq R φ n Y)
  exact Functor.isoWhiskerLeft _ eX ≪≫ (Functor.associator _ _ C).symm ≪≫
    Functor.isoWhiskerRight (moduleEvalG R φ f n) C ≪≫
    Functor.associator _ _ C ≪≫
    Functor.isoWhiskerLeft _
      (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) f)) ≪≫
    (Functor.associator _ D _).symm ≪≫ Functor.isoWhiskerRight eY.symm _

section RecoverSingle

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Recover an ordinary functor comparison through the fully faithful degree-zero embedding.
Source: Stacks 06YY (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def ordinaryRecoverSingleIso (e : F.mapDerivedCategory ≅ G.mapDerivedCategory) : F ≅ G :=
  let h := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor D 0)).whiskeringRight C
  h.preimageIso ((F.mapDerivedCategorySingleFunctor 0).symm ≪≫
      Functor.isoWhiskerLeft _ e ≪≫ G.mapDerivedCategorySingleFunctor 0)

end RecoverSingle

/-- The ordinary open comparison recovered from the specified derived open mate.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def ordinaryOpenEvaluation (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    extension R φ j ⋙ eval R φ X n ≅ eval R φ U n ⋙ StrictTower.moduleJ (R n) j :=
  ordinaryRecoverSingleIso _ _
    ((Functor.mapDerivedCategoryCompIso (extension R φ j) (eval R φ X n)).symm ≪≫
      evalJ R φ j n ≪≫
      Functor.mapDerivedCategoryCompIso (eval R φ U n) (StrictTower.moduleJ (R n) j))

/-- The actual open comparison, obtained from ordinary evaluation and degree zero.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-ordinary-evaluation-comparisons). -/
def ordinaryOpenComparison (n : ℕ) : OrdinaryOpenComparison R φ n := by
  intro U X j _
  unfold StrictTower.J
  let C := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0
  let D := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) U) 0
  let eX := eqToIso (ordinaryRealization_eq R φ n X)
  let eU := eqToIso (ordinaryRealization_eq R φ n U)
  exact Functor.isoWhiskerLeft _ eX ≪≫ (Functor.associator _ _ C).symm ≪≫
    Functor.isoWhiskerRight (ordinaryOpenEvaluation R φ n j) C ≪≫
    Functor.associator _ _ C ≪≫
    Functor.isoWhiskerLeft _ (ordinaryConstantSingleComparison (StrictTower.moduleJ (R n) j)) ≪≫
    (Functor.associator _ D _).symm ≪≫ Functor.isoWhiskerRight eU.symm _

end AlgebraicGeometry.ProEtale.VaryingRing
