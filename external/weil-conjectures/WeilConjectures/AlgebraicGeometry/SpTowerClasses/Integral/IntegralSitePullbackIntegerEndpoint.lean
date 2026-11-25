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
import WeilConjectures.WeilSheaf.FieldCoefficientTateTwist
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackIntegerEndpointMate
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralSitePullbackIntegerEndpointInverseImage

/-! # Integer endpoint in the change-of-site pullback square

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

/-- Integer endpoint square for the etale-to-pro-etale pullback.

Source: Stacks Project, Tag 00WX, and the integer endpoint part of the
change-of-site construction in the classes proof.
(blueprint: lem-sp-integral-site-pullback-integer-endpoint).

Proof: transpose through the two inverse-image adjunctions and the
constant-sheaf adjunction. The two resulting maps are the same constant-section
map on every base-changed chart, so adjunction injectivity proves the equality.
This endpoint identity is a strict substatement of the conjunction in
`integral_site_pullback_endpoints`.
-/
theorem integral_site_pullback_integer_endpoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
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
        (comparisonUpperStar AddCommGrpCat.{u + 1} X).map zEt)  := by
  dsimp
  let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let B := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let AY := (constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let BX := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let zEt := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
  let z := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv AY BX).symm
    (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let u2 : (upperStar AddCommGrpCat.{u + 1} f).obj AY ⟶ BX := by
    change (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj AY ⟶ BX
    exact proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have h := CategoryTheory.conjugateIsoEquiv_symm_hom_app_comp_map_comp
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (comparisonAdjunction AddCommGrpCat.{u + 1} Y)
    (comparisonAdjunction AddCommGrpCat.{u + 1} X)
    (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).symm
    (u₁ := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) (u₂ := u2) (v := (integerComparison Y).hom)
    (v' := (integerComparison X).hom)
  have h' := h (by
    simpa [zEt, u2, proEtaleConstantInverseImageMap]
      using integral_site_pullback_integer_endpoint_mate f)
  have hz : u2 = z := by
    simpa [u2, z] using
      (integral_site_pullback_integer_endpoint_inverse_image f).symm
  have hk : (comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f).hom.app A =
      ((conjugateIsoEquiv
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).comp
          (comparisonAdjunction AddCommGrpCat.{u + 1} X))
        ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).comp
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f))).symm
        (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).symm).hom.app A := rfl
  rw [hk]
  apply (cancel_mono
    ((comparisonUpperStar AddCommGrpCat.{u + 1} X).map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
      (integerComparison X).hom)).mp
  rw [Category.assoc, Category.assoc, h']
  rw [← (upperStar AddCommGrpCat.{u + 1} f).map_comp_assoc]
  simp only [Category.assoc]
  rw [(integerComparison Y).inv_hom_id]
  simp
  simpa [z] using hz

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
