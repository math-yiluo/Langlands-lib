/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
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
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackIntegerEndpoint
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackUnitsEndpoint

/-! # Integer and units endpoints in the change-of-site pullback square

Source: Stacks Project, Tag 00WX; the integral class construction in
sec-smooth-purity/sk-prop-sp-tower-geometric, classes proof (2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The two endpoint squares in the canonical etale-to-pro-etale pullback square.
The first equality concerns only constant integer sheaves; the second concerns only
units sheaves. There is no line bundle, cohomology class or derived-category map in
this statement.

Source: Stacks Project, Tag 00WX, the change-of-site construction in
sec-smooth-purity/sk-prop-sp-tower-geometric, classes proof (2).
(blueprint: lem-sp-integral-site-pullback-endpoints).

Proof: comparisonUpperStarCompUpperStarIso is the mate of the canonical commuting
square of direct images, oriented from f_proet^* nu_Y^* to nu_X^* f_et^*.
For integers, transpose the claimed equality through the two composite
inverse-image adjunctions, followed by the constant-sheaf adjunction. The definition
of integerComparison by uniqueness of left adjoints and the definition of
upperStarConstantSheafIso turn both transposes into the map sending each integer k
to the constant section k on the base-changed chart. Thus the maps agree.
For units, transpose through the same composite inverse-image adjunctions.
cartierUnitsComparison is adjoint to the identity on units of each etale chart.
By ha, a is adjoint to pullback along the fibre-product projection.
upperStarGmSheafToGmSheaf has precisely the same adjoint on etale charts, by its
definition. The direct-image compositor in the mate is the chart base-change
isomorphism, whose first projection commutes with the two projections used here.
Both transposes therefore pull back a unit along the same projection; naturality
of the adjunction gives the second equality. All checks are on arbitrary charts,
so empty schemes, nonflat f and noninvertible full-units comparisons cause no
exception.
-/
theorem integral_site_pullback_endpoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : (upperStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf Y) ⟶
      Scheme.proEtaleUnitsSheaf X)
    (ha : ∀ (U : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleUnitsSheaf Y).obj.obj U),
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _) a).hom.app
          U x =
        ULift.up (Additive.ofMul
          (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul))) :
    let κ := comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f
    let z := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
      (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    let zEt := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
    ((upperStar AddCommGrpCat.{u + 1} f).map (integerComparison Y).inv ≫
        κ.hom.app ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      z ≫ (integerComparison X).inv ≫
        (comparisonUpperStar AddCommGrpCat.{u + 1} X).map zEt) ∧
    (κ.inv.app Y.gmSheaf ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (cartierUnitsComparison Y) ≫ a =
      (comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          (Scheme.upperStarGmSheafToGmSheaf f) ≫ cartierUnitsComparison X) := by
  constructor
  · exact integral_site_pullback_integer_endpoint f
  · exact integral_site_pullback_units_endpoint f a ha

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
