/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # The localizing predicate for localized tensor comparisons

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: def-pc-localized-tensor-comparison-property).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- All K-flat representatives of X satisfy tensor comparison in every degree.
This is an explicit predicate; it assumes no comparison map to be invertible.
Source: Stacks Project, Tag 0DJA(1).
(blueprint: def-pc-localized-tensor-comparison-property). -/
def localizedTensorComparisonProperty : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  fun X ↦ ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
    Nonempty (DerivedCategory.Q.obj U ≅ X) →
    (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
    ∀ (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ),
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i)

end ModuleCat
