/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulModelsSupplement
public import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # StrictScalarKoszulInstances for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-strict-scalar-koszul-instances).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

/-- Coproducts supply the tensor product of two integer-graded objects.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem gradedTensorCache {D : Type*} [Category D] [MonoidalCategory D]
    [HasCoproducts.{0} D] (X Y : GradedObject ℤ D) : X.HasTensor Y := by
  infer_instance

/-- Closed tensor preserves the coproducts for the left-associated triple tensor.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem gradedGoodTensorLeftCache {D : Type*} [Category D] [Abelian D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [HasCoproducts.{0} D] (X Y Z : GradedObject ℤ D) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := by
  infer_instance

/-- Closed tensor preserves the coproducts for the right-associated triple tensor.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem gradedGoodTensorRightCache {D : Type*} [Category D] [Abelian D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [HasCoproducts.{0} D] (X Y Z : GradedObject ℤ D) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := by
  infer_instance

/-- Fourfold graded tensor maps are determined by their summand inclusions.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem gradedFourCache {D : Type*} [Category D] [Abelian D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [HasCoproducts.{0} D] (W X Y Z : GradedObject ℤ D) :
    GradedObject.HasTensor₄ObjExt W X Y Z := by
  infer_instance

/-- Tensoring on the left preserves the empty colimit.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem tensorPreservesEmptyLeftCache {D : Type*} [Category D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] (X : D) :
    PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X) := by
  infer_instance

/-- Symmetry transfers empty-colimit preservation to tensoring on the right.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem tensorPreservesEmptyRightCache {D : Type*} [Category D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [SymmetricCategory D] (X : D) :
    PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X) := by
  infer_instance

/-- The canonical site tensor structure on module sheaves.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
@[instance_reducible] def cachedModuleMonoidal (O : Sheaf J CommRingCat.{u}) :
    MonoidalCategory (Modules O) := SheafOfModules.monoidalCategory O

attribute [local instance] cachedModuleMonoidal

/-- The symmetry of the canonical site tensor on module sheaves.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
@[instance_reducible] def cachedModuleSymmetric (O : Sheaf J CommRingCat.{u}) :
    SymmetricCategory (Modules O) := by
  let := SheafOfModules.monoidalCategory O
  exact SheafOfModules.symmetricCategory O

attribute [local instance] cachedModuleSymmetric

/-- The additive tensor witness supplied by the existing closed tensor theorem.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
theorem cachedModulePreadditive (O : Sheaf J CommRingCat.{u}) :
    MonoidalPreadditive (Modules O) := by
  let := SheafOfModules.monoidalCategory O
  exact Classical.choice (SheafOfModules.tensorClosed O).1

attribute [local instance] cachedModulePreadditive

/-- The existing tensor-Hom adjunction for module sheaves.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
@[instance_reducible] def cachedModuleClosed (O : Sheaf J CommRingCat.{u}) :
    MonoidalClosed (Modules O) := by
  let := SheafOfModules.monoidalCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  exact SheafOfModules.monoidalClosed (R := O)

attribute [local instance] cachedModuleClosed

/-- The coproduct total tensor on integer cochain complexes of module sheaves.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
@[instance_reducible] def cachedComplexMonoidal (O : Sheaf J CommRingCat.{u}) :
    MonoidalCategory (ringedSiteComplex O) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  infer_instance

attribute [local instance] cachedComplexMonoidal

/-- The graded braiding on integer cochain complexes of module sheaves.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
@[instance_reducible] def cachedComplexBraided (O : Sheaf J CommRingCat.{u}) :
    BraidedCategory (ringedSiteComplex O) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  infer_instance

attribute [local instance] cachedComplexBraided

/-- The existing signed tensor-Hom adjunction on integer cochain complexes.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Use the canonical site tensor, symmetric structure and tensor-Hom adjunction of
module sheaves. The monoidal preadditivity witness is the first component of tensorClosed; the
closed structure is the existing monoidalClosed definition.
Proof step 2: The sheaf module category is Grothendieck abelian, hence has the coproducts needed
for the total tensor. Synthesize the monoidal and braided structures of cochain complexes, and
use ringedComplexClosed for its chosen closed structure.
(blueprint: lem-f5-strict-scalar-koszul-instances). -/
@[instance_reducible] def cachedComplexClosed (O : Sheaf J CommRingCat.{u}) :
    MonoidalClosed (ringedSiteComplex O) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  exact ringedComplexClosed O

attribute [local instance] cachedComplexClosed

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache

end CategoryTheory.FlatScalarKoszul
