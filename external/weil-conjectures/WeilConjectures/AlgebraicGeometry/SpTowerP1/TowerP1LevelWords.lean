/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1TensorCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.EtaleWords.TowerP1EtaleWords
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Normalized tensor coordinates for projective-line level comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels
(blueprint: def-sp-p1-level-words).

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The actual finite coefficient ring in fixed-module coordinates.
Source: Levels (blueprint: def-sp-p1-level-words). -/
abbrev levelRing := ULift.{u + 1} (SpTowerShriek.R l E n)

/-- The exact comparison inverse image followed by associated-module realization.
Source: Levels (blueprint: def-sp-p1-level-words). -/
abbrev nu (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategory ⋙
    (realization l E n T).mapDerivedCategory

/-- The annihilating exponent in the lifted ring is the recorded quotient equation.
Source: coefficient convention (blueprint: def-sp-p1-level-words). -/
abbrev levelAnnihilates : ((l ^ (n + 1) : ℕ) : levelRing l E n) = 0 :=
  ULift.ext (SpTowerClasses.coefficient_annihilates l E n)

/-- An etale expression, its tower expression, and their specified comparison arrow.
The arrow is built recursively from site mates and evaluation; it is not freely chosen
at the endpoints of any asserted equation.
Source: Levels (blueprint: def-sp-p1-level-words). -/
structure LevelWord (T : Scheme.{u}) where
  tower : SpTowerShriek.D l E T
  etale : Etale.DerivedCategoryModule (levelRing l E n) T
  comparison : (nu l E n T).obj etale ⟶ (SpTowerShriek.Ev l E T n).obj tower

/-- The word supplied by any retained origin, using precisely its specified witness.
Source: Levels (blueprint: def-sp-p1-level-words). -/
def originWord (b : SpTowerShriek.Base l E) {T : Scheme.{u}}
    {K : SpTowerShriek.D l E T} (o : SpTowerShriek.Origin l E b T n K) :
    LevelWord l E n T where
  tower := K
  etale := o.witness.complex.obj
  comparison := ((realization l E n T).mapDerivedCategory.mapIso o.witness.iso ≪≫
    o.realization).hom

/-- Inverse-image word, through the canonical site pullback and pullEvaluation.
Source: Levels (blueprint: def-sp-p1-level-words). -/
def pullWord (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (c : GeometricCoordinates l E n f)
    (K : LevelWord l E n Y) : LevelWord l E n X where
  tower := (SpTowerShriek.pull l E b g).obj K.tower
  etale := (EtaleWords.pull (levelRing l E n) f).obj K.etale
  comparison := (realization l E n X).mapDerivedCategory.map
      ((exactSitePull l E n f).hom.app K.etale) ≫
    c.pull.inv.app _ ≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map K.comparison ≫
    (g.pullEvaluation n).inv.app K.tower

/-- Direct-image word, through the fixed canonical site mate and pushEvaluation.
Its comparison is defined even before its bounded-domain invertibility is proved.
Source: Levels (blueprint: def-sp-p1-level-words). -/
def pushWord (b : SpTowerShriek.Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (c : GeometricCoordinates l E n f)
    (K : LevelWord l E n X) : LevelWord l E n Y where
  tower := (SpTowerShriek.push l E b g).obj K.tower
  etale := (EtaleWords.push (levelRing l E n) f).obj K.etale
  comparison := (realization l E n Y).mapDerivedCategory.map
      ((exactSitePush l E n f).app K.etale) ≫
    c.derived.inv.app _ ≫
    (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).rightDerivedFunctor.map
      K.comparison ≫ (g.pushEvaluation n).inv.app K.tower

/-- Tensor word, using the fixed site's monoidal comparison, normalized realization,
and the section-model tensorEvaluation in that order.
Source: Levels (blueprint: def-sp-p1-level-words). -/
def tensorWord (b : SpTowerShriek.Base l E) {T : Scheme.{u}}
    (c : TensorCoordinates l E n b T) (K L : LevelWord l E n T) : LevelWord l E n T where
  tower := (SpTowerShriek.tensor l E b T).obj (K.tower, L.tower)
  etale := ((EtaleWords.tensor (levelRing l E n) T).obj K.etale).obj L.etale
  comparison := (realization l E n T).mapDerivedCategory.map
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} (levelRing l E n)) K.etale).hom.app L.etale) ≫
    c.derived.hom.app
      ((Functor.mapDerivedCategory
        (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T)).obj K.etale,
       (Functor.mapDerivedCategory
        (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T)).obj L.etale) ≫
    ((b.calculus T).levelClosed n).tensor.map (Prod.mkHom K.comparison L.comparison) ≫
    ((b.calculus T).tensorEvaluation n).inv.app (K.tower, L.tower)

/-- Equality of the actual evaluated map with nu-star of its etale word, with the
canonical endpoint comparisons invertible. This is a commuting square of arrows,
not a repetition of an input geometry field.
Source: Levels (blueprint: def-sp-p1-level-words). -/
def WordComparison {T : Scheme.{u}} (K L : LevelWord l E n T)
    (f : K.tower ⟶ L.tower) (g : K.etale ⟶ L.etale) : Prop :=
  IsIso K.comparison ∧ IsIso L.comparison ∧
    K.comparison ≫ (SpTowerShriek.Ev l E T n).map f =
      (nu l E n T).map g ≫ L.comparison

end AlgebraicGeometry.ProEtale.SpTowerP1
