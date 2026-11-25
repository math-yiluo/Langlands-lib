/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1LevelWords
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleWords
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-coefficient-coordinates).

The coordinates retain the canonical associated-module-sheaf functor. Its tensor
comparison is fixed on scalar-unit pure tensors, on total-complex summands, and
on K-flat representatives. Thus the final level equations cannot be satisfied
by choosing unrelated isomorphisms of their endpoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

/-- The ordinary site/realization comparison of the constant module and Tate line,
normalized on constants and on the same root section on every pro-etale test.
Source: Levels, root comparison (blueprint: def-sp-p1-coefficient-coordinates). -/
structure CoefficientCoordinates (T : Scheme.{u})
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) where
  unit : (realization l E n T).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).obj
        (Etale.ordinaryFiniteConstant (levelRing l E n) T)) ≅
    (SpTowerShriek.ev l E T n).obj
      (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))
  unit_sections : ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : levelRing l E n),
    unit.hom.val.app W
      (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W
        (((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).obj
          (Etale.ordinaryFiniteConstant (levelRing l E n) T)).obj.map f.op
          (((comparisonAdjunction (ModuleCat.{u + 1} (levelRing l E n)) T).unit.app
            (Etale.ordinaryFiniteConstant (levelRing l E n) T)).hom.app U
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of (levelRing l E n)
                (levelRing l E n)))).app U a)))) =
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (levelRing l E n)))).app W a
  line : (realization l E n T).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).obj
        (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (levelRing l E n)
          (levelAnnihilates l E n))) ≅ SpTowerClasses.finiteLine l E T n
  line_sections : ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop) (a : levelRing l E n)
    (z : (T.rootsOfUnitySheaf (l ^ (n + 1))).obj.obj U),
    line.hom.val.app W
      (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W
        (((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).obj
          (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (levelRing l E n)
            (levelAnnihilates l E n))).obj.map f.op
          (((comparisonAdjunction (ModuleCat.{u + 1} (levelRing l E n)) T).unit.app
            (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (levelRing l E n)
              (levelAnnihilates l E n))).hom.app U
                (Scheme.finiteEtaleTateOneGenerator (levelRing l E n) (l ^ (n + 1)) T
                  (levelAnnihilates l E n) U a z)))) =
    Scheme.tateFiniteTensor T l (levelRing l E n) n (SpTowerClasses.finiteScalar l E n)
      W.unop
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (levelRing l E n)))).app W a)
      ((ProEtale.cartierRootsIso T (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) hT).hom.hom.app W
        (((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
          (T.rootsOfUnitySheaf (l ^ (n + 1)))).obj.map f.op
          (((comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
            (T.rootsOfUnitySheaf (l ^ (n + 1)))).hom.app U z)))

attribute [local irreducible] realization CategoryTheory.Functor.mapDerivedCategory

/-- Single-complex compatibility of the composite exact comparison functor.
Source: Levels (blueprint: def-sp-p1-coefficient-coordinates). -/
def nuSingle (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))) :
    (nu l E n T).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((realization l E n T).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).obj M)) :=
  (realization l E n T).mapDerivedCategory.mapIso
    ((Functor.mapDerivedCategorySingleFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T) 0).app M) ≪≫
    ((realization l E n T).mapDerivedCategorySingleFunctor 0).app _

/-- The constant word; the only coefficient comparison sends one to one.
Source: Levels (blueprint: def-sp-p1-coefficient-coordinates). -/
def unitWord (T : Scheme.{u})
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))} (c : CoefficientCoordinates l E n T hT) :
    LevelWord l E n T where
  tower := SpTowerClasses.unit T (SpTowerClasses.Arings l E T)
  etale := Etale.ordinaryFiniteUnit (levelRing l E n) T
  comparison := (nuSingle l E n T _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso c.unit ≪≫
    (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm).hom

/-- The shifted line word; its transport includes lineEvaluation and exact shift maps.
Source: Levels, twists and shifts (blueprint: def-sp-p1-coefficient-coordinates). -/
def lineWord {T : Scheme.{u}} (t : SpTowerClasses.Chern l E T)
    {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))} (c : CoefficientCoordinates l E n T hT) :
    LevelWord l E n T where
  tower := (SpTowerClasses.line l E t)⟦(2 : ℤ)⟧
  etale := EtaleWords.line (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n) T
  comparison := (((nu l E n T).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (nuSingle l E n T _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso c.line ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (SpTowerClasses.lineEvaluation l E t n).symm ≪≫
        (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm) ≪≫
    (((SpTowerShriek.Ev l E T n).commShiftIso (2 : ℤ)).app _).symm).hom

end AlgebraicGeometry.ProEtale.SpTowerP1
