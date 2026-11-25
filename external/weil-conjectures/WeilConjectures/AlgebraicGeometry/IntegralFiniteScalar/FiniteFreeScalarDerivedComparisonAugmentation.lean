/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj

/-! Augmentation part of the finite-free scalar comparison.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

set_option linter.unusedVariables false in
/-- The pulled-back finite-free augmentation is a quasi-isomorphism.

The point pullback preserves the cokernel cofork and the two endpoint
finite-free presentations; exact section transport identifies its augmentation with
`augmentation Λ S Z`.
-/
theorem finiteFreeScalarDerivedComparison_augmentation
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hS : S.ShortExact) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (Z : Scheme.{u}) : QuasiIso (augmentation Λ S Z) := by
  have : PreservesFiniteLimits (CochainComplex.singleFunctor (PointModules Λ) 0) :=
    inferInstanceAs
      (PreservesFiniteLimits (HomologicalComplex.single (PointModules Λ) (.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor (PointModules Λ) 0) :=
    inferInstanceAs
      (PreservesFiniteColimits (HomologicalComplex.single (PointModules Λ) (.up ℤ) 0))
  have : QuasiIso (CochainComplex.monoCokernelAugmentation S) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex
      (hS.map_of_exact (CochainComplex.singleFunctor (PointModules Λ) 0))
  have : PreservesFiniteLimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.1
  have : PreservesFiniteColimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.2.1
  have : PreservesFiniteLimits (sfbPullbackFromPoint Z) := by
    change PreservesFiniteLimits (pointUpperStar ⋙ (toSpecZ Z)^*[Ab.{u + 1}])
    infer_instance
  have : PreservesFiniteColimits (sfbPullbackFromPoint Z) := by
    change PreservesFiniteColimits (pointUpperStar ⋙ (toSpecZ Z)^*[Ab.{u + 1}])
    infer_instance
  have : PreservesFiniteLimits (pointPull Λ Z) := inferInstance
  have : PreservesFiniteColimits (pointPull Λ Z) := inferInstance
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (CochainComplex.monoCokernelAugmentation S) (pointPull Λ Z)

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
