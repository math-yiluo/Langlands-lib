/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
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
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.LineBundleTowerPullbackSquare
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralTowerPullbackSquare

/-! # Integral line-bundle classes and geometric pullback

Source: blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
classes proof (2), and the integral extension argument in steps 1--3 of
lem-sp-tower-chern-pullback (blueprint: lem-sp-tower-integral-class-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Integral line-bundle classes commute with pullback to full units, in the ordinary
 derived category of abelian towers. No torsion coefficient or root comparison occurs.
Source: blueprint classes proof (2); lem-sp-tower-chern-pullback, steps 1--3
(blueprint: lem-sp-tower-integral-class-pullback).

Proof: lineBundle_proEtaleClass_pullback gives the class identity before making
constant towers. It follows from the already proved arbitrary-scheme Picard
cohomology naturality and the ordinary integer and units endpoint squares.
Functor.compConstIso identifies inverse image of a constant tower with the constant
tower of inverse image. Exact-functor Ext compatibility with composition and
isomorphisms transports the sheaf identity through this comparison. The components
of integerPull and unitsPull are exactly the endpoints in that identity. Finally,
cancel the inverse single comparison on the source; this produces precisely the
single and shift comparisons in integerDerivedPull and unitsDerivedPull.
Empty schemes, trivial bundles and nonflat morphisms require no extra assumptions. -/
theorem tower_integralClass_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    (abPull f).mapDerivedCategory.map (lineBundleClass Y (Scheme.Pic.ofIsInvertible L)) ≫
        unitsDerivedPull f =
      integerDerivedPull f ≫
        lineBundleClass X (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L)) := by
  exact normalized_integral_tower_square (towerIntegral_normalizedSquare f L)

end AlgebraicGeometry.ProEtale.SpTowerClasses
