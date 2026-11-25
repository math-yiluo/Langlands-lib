/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterEvaluationData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterDegreeZeroData
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.FreeParameterScalarMaps

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-scalar-maps). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Mod.monoidalCategory Mod.monoidalCategoryStruct
  Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 20000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

section CachedInstances
variable (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
variable (T : Scheme.{u})
private theorem schemeFour : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Modules A T)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem schemeGood12 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem schemeGood23 : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Modules A T)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem schemeLeft : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).obj X) := inferInstance
private theorem schemeRight : ∀ (X : Modules A T),
    PreservesColimitsOfShape ℤ ((curriedTensor (Modules A T)).flip.obj X) := inferInstance
end CachedInstances
attribute [local instance] schemeFour schemeGood12 schemeGood23 schemeLeft schemeRight

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

section Scalars
variable (S : Profinite.CondensedRing.{u}) [IsCommMonObj S.X]
  (φ : R.X ⟶ S.X) [IsMonHom φ]

/-- K-flat derived extension of scalars, with its recorded scalar adjunction.
Source: Stacks 07A6 (blueprint: def-sfb-free-parameter-scalar-maps). -/
abbrev extendPoint := (Mod.extendScalars φ).leftDerivedFunctor

/-- The derived tensorator of scalar extension, normalized by scalar units at the
ordinary level. This uses preservation of flat objects, never exact scalar extension.
Source: Stacks 07A4 (blueprint: def-sfb-free-parameter-scalar-maps). -/
def scalarTensor (K L : DerivedCategory (PointModules R)) :
    (extendPoint R S φ).obj K ⊗ (extendPoint R S φ).obj L ≅
      (extendPoint R S φ).obj (K ⊗ L) :=
  letI := (Mod.exists_extendScalarsMonoidal φ).choose
  letI := Mod.extendScalars_preservesFlat φ
  letI := (Mod.extendRestrictAdjunction φ).isLeftAdjoint
  letI := (Mod.extendScalars φ).leftDerivedFunctorMonoidal
  Functor.Monoidal.μIso (extendPoint R S φ) K L


omit [IsCommMonObj S.X] in
set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  DerivedCategory.singleFunctors Profinite.CondensedAction.InternalBar.free
  Mod.comap Mod.extendScalars Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.upperStar CondensedRing.derivedComapUpperStarIso
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory

attribute [local irreducible] scalarTensor restrictPointPullD

attribute [local irreducible] scalarPullComparison

end Scalars

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
