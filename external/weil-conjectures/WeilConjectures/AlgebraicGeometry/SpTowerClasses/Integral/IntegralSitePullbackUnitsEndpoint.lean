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
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackUnitsEndpointCanonical

/-! # Units endpoint in the change-of-site pullback square

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

/-- Units endpoint square for the etale-to-pro-etale pullback.

Source: Stacks Project, Tag 00WX, and the units endpoint part of the
change-of-site construction in the classes proof.
(blueprint: lem-sp-integral-site-pullback-units-endpoint).

Proof: transpose through the two inverse-image adjunctions. The hypothesis on
`a`, the adjunction definition of `cartierUnitsComparison`, and the definition
of `upperStarGmSheafToGmSheaf` all give pullback of a unit along the same
fibre-product projection on every chart. Adjunction injectivity proves the
identity. This endpoint identity is a strict substatement of the conjunction
in `integral_site_pullback_endpoints`.
-/
theorem integral_site_pullback_units_endpoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : (upperStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf Y) ⟶
      Scheme.proEtaleUnitsSheaf X)
    (ha : ∀ (U : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleUnitsSheaf Y).obj.obj U),
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _) a).hom.app
          U x =
        ULift.up (Additive.ofMul
          (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul))) :
    let κ := comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f
    (κ.inv.app Y.gmSheaf ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (cartierUnitsComparison Y) ≫ a =
      (comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          (Scheme.upperStarGmSheafToGmSheaf f) ≫ cartierUnitsComparison X) := by
  let a₀ := towerIntegral_unitsSheafPull f
  have ha₀ : a = a₀ := by
    apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
    ext U x
    exact (ha U x).trans (towerIntegral_unitsPull_adjoint f U x).symm
  rw [ha₀]
  exact integral_site_pullback_units_endpoint_canonical f

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
