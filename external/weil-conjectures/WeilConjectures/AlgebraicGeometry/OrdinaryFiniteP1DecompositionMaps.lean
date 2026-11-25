/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Canonical arrows for the inverse-twist projective-line decomposition

The unit and Chern adjoint are explicit, independently of the proof of their splitting.
The comparison and untwisting lemmas use this common interface.
Source: main-20261015, thm-amb-p1-decomposition.md and its proof
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

set_option backward.isDefEq.respectTransparency false in
/-- The compact normalized signed-twist interface, retaining its public projections.
Source: Stacks Tags 03PK and 03Q1 (blueprint: lemma-cohomology-projective-line-trace). -/
structure P1DecompositionTwistTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) where
  roots : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) →
    ((upperStar AddCommGrpCat.{u + 1} f).obj (Y.rootsOfUnitySheaf N) ≅
      X.rootsOfUnitySheaf N)
  line : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IsUnit (N : Γ(Y, ⊤)) → IsUnit (N : Γ(X, ⊤)) → ∀ a : ℤ,
    (upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a
  product : ∀ (T : Scheme.{u}), IsUnit (N : Γ(T, ⊤)) →
    (Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1) ≅
      Scheme.finiteEtaleTateSheaf A N T hA (1 + -1))
  roots_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))),
    (upperStar AddCommGrpCat.{u + 1} f).map (kernel.ι (N • 𝟙 Y.gmSheaf)) ≫
        Scheme.upperStarGmSheafToGmSheaf f =
      (roots f hY).hom ≫ kernel.ι (N • 𝟙 X.gmSheaf)
  line_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
      (W : Y.Etaleᵒᵖ) (a : A) (z : (Y.rootsOfUnitySheaf N).obj.obj W),
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      (line f hY hX 1).hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N Y hA W a z) =
    Scheme.finiteEtaleTateOneGenerator A N X hA
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).op.obj W) a
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (roots f hY).hom).hom.app W z)
  zero_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))),
    line f hY hX 0 =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A)
  power_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (n : ℕ),
    line f hY hX (.ofNat (n + 2)) =
      asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
        (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))
        (Scheme.finiteEtaleTateLine Y N A hA)) ≪≫
      tensorIso (line f hY hX (.ofNat (n + 1))) (line f hY hX 1)
  negative_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (n : ℕ),
    (upperStar (ModuleCat.{u + 1} A) f).map
        ((ihom.ev (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A N Y hA 0)) ≫ (line f hY hX 0).hom =
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f)
          (Scheme.finiteEtaleTateSheaf A N Y hA (.ofNat (n + 1)))
          (Scheme.finiteEtaleTateSheaf A N Y hA (.negSucc n)) ≫
        tensorHom (line f hY hX (.ofNat (n + 1))).hom (line f hY hX (.negSucc n)).hom ≫
        (ihom.ev (Scheme.finiteEtaleTateSheaf A N X hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A N X hA 0)
  product_normalization : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
    (product T hT).hom ≫ eqToHom
        (congrArg (Scheme.finiteEtaleTateSheaf A N T hA) (add_neg_cancel (1 : ℤ))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app
        (Scheme.finiteEtaleTateSheaf A N T hA 0)

/-- Keep precisely the compact record's projections of full normalized transport.
Source: Stacks Tags 03PK and 03Q1 (auxiliary; not a blueprint node). -/
def p1DecompositionTransportOfData (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : Scheme.FiniteEtaleTwistPullbackData A N hA) :
    P1DecompositionTwistTransport A N hA :=
  { roots := t.r
    line := t.c
    product := fun T hT ↦ t.p T hT 1 (-1)
    roots_normalization := t.laws.2.1
    line_normalization := t.laws.2.2.1
    zero_normalization := t.laws.2.2.2.1
    power_normalization := t.laws.2.2.2.2.1
    negative_normalization := t.laws.2.2.2.2.2.1
    product_normalization := fun T hT ↦ t.laws.2.2.2.2.2.2.2.2.2.2.2.2.2.1 T hT 0 }

/-- Project the already constructed fully normalized transport into the compact
interface, keeping each characterizing equation and making no additional choice.
Source: Stacks Tags 03PK and 03Q1 (blueprint: lemma-cohomology-projective-line-trace). -/
@[irreducible]
def p1DecompositionTwistTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    P1DecompositionTwistTransport A N hA :=
  p1DecompositionTransportOfData A N hA (Scheme.finiteEtaleTwistPullbackData A N hN hA)

/-- The signed twist pullback with its roots, pure-tensor and negative-evaluation
normalizations retained in `p1DecompositionTwistTransport`.
Source: Stacks Tags 03PK and 03Q1 (blueprint: lemma-cohomology-projective-line-trace). -/
def p1DecompositionSheafPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a : ℤ) :
    (upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateSheaf A N Y hA a) ≅
      Scheme.finiteEtaleTateSheaf A N X hA a :=
  (p1DecompositionTwistTransport A N hN hA).line
    f hY ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) a

/-- The inverse-line product, whose hom is characterized as internal-Hom evaluation.
Source: Stacks Tag 03PK (blueprint: lemma-cohomology-projective-line-trace). -/
def p1DecompositionSheafProduct (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1) ≅
      Scheme.finiteEtaleTateSheaf A N T hA (1 + -1) :=
  (p1DecompositionTwistTransport A N hN hA).product T hT

/-- A finite signed twist placed in degree zero and shifted by an integer.
Source: the definition K=A_S(-1)[-2] (blueprint: lemma-cohomology-projective-line-trace). -/
abbrev p1DecompositionTwist (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (a b : ℤ) :
    DerivedCategoryModule A T :=
  (ordinaryFiniteDegreeZero A T (Scheme.finiteEtaleTateSheaf A N T hA a))⟦b⟧

/-- Shift a comparison between functors, without unfolding its concrete categories.
Source: functoriality of the shift (auxiliary; not a blueprint node). -/
@[irreducible]
def p1DecompositionShiftedComparison {C D C₀ D₀ : Type*}
    [Category C] [Category D] [Category C₀] [Category D₀]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (single : C₀ ⥤ C) (single' : D₀ ⥤ D)
    (pull : C₀ ⥤ D₀) (comp : single ⋙ F ≅ pull ⋙ single')
    (L : C₀) (M : D₀) (e : pull.obj L ≅ M) (b : ℤ) :
    F.obj ((single.obj L)⟦b⟧) ≅ (single'.obj M)⟦b⟧ :=
  (F.commShiftIso b).app _ ≪≫
    (shiftFunctor _ b).mapIso (comp.app L ≪≫ single'.mapIso e)

/-- Derived inverse image of a signed shifted twist, with the canonical shift and
degree-zero comparisons and the normalized sheaf comparison.
Source: Stacks Tag 03Q1 (blueprint: lemma-cohomology-projective-line-trace). -/
def p1DecompositionTwistPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a b : ℤ) :
    (ordinaryFinitePullback A f).obj (p1DecompositionTwist A N hA Y a b) ≅
      p1DecompositionTwist A N hA X a b :=
  letI : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  p1DecompositionShiftedComparison (ordinaryFinitePullback A f)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} A) f)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f)
    (Scheme.finiteEtaleTateSheaf A N Y hA a) (Scheme.finiteEtaleTateSheaf A N X hA a)
    (p1DecompositionSheafPullback A N hN hA f hY a) b

/-- Compute the tensor of the positive line and its sheaf dual in degree zero.
The positive line is flat by its normalized inverse-product isomorphism.
Source: the evaluation step in the node (blueprint: lemma-cohomology-projective-line-trace). -/
@[irreducible]
def p1DecompositionDegreeZeroTensor (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj (ordinaryFiniteLine A N hA T)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf A N T hA 1 ⊗ Scheme.finiteEtaleTateSheaf A N T hA (-1)) :=
  singleFunctorObjTensorIso (Scheme.finiteEtaleTateSheaf A N T hA 1)
    (Scheme.finiteEtaleTateSheaf A N T hA (-1))
    (ObjectProperty.flat_of_tensorIso (p1DecompositionSheafProduct A N hN hA T hT))

/-- Evaluate the degree-zero dual against the positive line, using symmetry and
then the actual internal-Hom evaluation, after the canonical flat tensor comparison.
Source: the evaluation step in the node (blueprint: lemma-cohomology-projective-line-trace). -/
@[irreducible]
def p1DecompositionDegreeZeroEvaluation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1)))).obj
      (ordinaryFiniteLine A N hA T) ⟶ ordinaryFiniteUnit A T :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app _).app _ ≫
    (p1DecompositionDegreeZeroTensor A N hN hA T hT).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((ihom.ev (Scheme.finiteEtaleTateSheaf A N T hA 1)).app (ordinaryFiniteConstant A T))

/-- Evaluation of A_T(-1)[-2] against A_T(1)[2]: cancel the shifts and apply
`p1DecompositionDegreeZeroEvaluation`.
Source: the evaluation in the defining adjoint of h
(blueprint: lemma-cohomology-projective-line-trace). -/
@[irreducible]
def p1DecompositionEvaluation (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ((ordinaryFiniteTensor A T).obj (p1DecompositionTwist A N hA T (-1) (-2))).obj
        ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶ ordinaryFiniteUnit A T :=
  (derivedTensorShiftIso (ModuleCat.{u + 1} A)
    ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N T hA (-1)))
    (ordinaryFiniteLine A N hA T) (-2) 2).hom ≫
    (shiftFunctorZero _ ℤ).hom.app _ ≫
    p1DecompositionDegreeZeroEvaluation A N hN hA T hT

end AlgebraicGeometry.Etale
