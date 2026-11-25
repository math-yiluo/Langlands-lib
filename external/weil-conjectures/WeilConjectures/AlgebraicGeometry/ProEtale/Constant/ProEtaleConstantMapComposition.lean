/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSectionMapComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Composition of constant inverse-image maps on the pro-etale site
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace Scheme

set_option linter.unusedVariables false in
/-- The constant-coefficient structure map is compatible with composition of morphisms.
-/
theorem proEtaleConstantInverseImageMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type (u + 1)) [CommRing A] :
    let D := ModuleCat.{u + 1} A
    let M := ModuleCat.of A A
    let A_X := (constantSheaf (ProEt.topology X) D).obj M
    let A_Y := (constantSheaf (ProEt.topology Y) D).obj M
    let A_Z := (constantSheaf (ProEt.topology Z) D).obj M
    proEtaleConstantInverseImageMap (f ≫ g) D M =
      (ProEtale.upperStarComp D f g).hom.app A_Z ≫
        (proEtaleSheafInverseImage f D).map
          (proEtaleConstantInverseImageMap g D M) ≫
        proEtaleConstantInverseImageMap f D M := by
  let D := ModuleCat.{u + 1} A
  let M := ModuleCat.of A A
  let A_Z := (constantSheaf (ProEt.topology Z) D).obj M
  let A_X := (constantSheaf (ProEt.topology X) D).obj M
  let adjg := ProEtale.upperStarLowerStarAdjunction D g
  let adjf := ProEtale.upperStarLowerStarAdjunction D f
  let adj := ProEtale.upperStarLowerStarAdjunction D (f ≫ g)
  have hκ := unit_conjugateEquiv (adjg.comp adjf) adj
    (ProEtale.upperStarComp D f g).hom A_Z
  rw [ProEtale.conjugateEquiv_upperStarComp_hom D f g] at hκ
  change (adj.homEquiv A_Z A_X).symm _ = _
  rw [proEtaleConstantDirectImageMap_comp]
  apply (adj.homEquiv A_Z A_X).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A_Z ≫ (ProEtale.lowerStar D (f ≫ g)).map _) ≫
    (ProEtale.lowerStar D (f ≫ g)).map _
  rw [← hκ, Category.assoc, ← (ProEtale.lowerStarComp D f g).hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A_Z A_X)
    ((ProEtale.upperStar D f).map
      ((adjg.homEquiv _ _).symm (proEtaleConstantDirectImageMap g D M)) ≫
        (adjf.homEquiv _ _).symm (proEtaleConstantDirectImageMap f D M)) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  rfl

end Scheme
end AlgebraicGeometry
