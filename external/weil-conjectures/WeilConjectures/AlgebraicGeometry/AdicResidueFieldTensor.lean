/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Exact field tensor and cohomological bounds

Source: Bhatt--Scholze, Remark 6.3.2
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalClosed.FunctorCategory
namespace AlgebraicGeometry.Scheme

private theorem sfbFieldTensor_exact (X : Scheme.{u}) (k : Type (u + 1)) [Field k]
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) :
    let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
    PreservesFiniteLimits (MonoidalCategory.tensorRight N) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight N) := by
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
  let := Sheaf.symmetricCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
  have hpre : PreservesFiniteLimits (MonoidalCategory.tensorRight N.obj) := by
    apply preservesFiniteLimits_of_evaluation
    intro U
    change PreservesFiniteLimits
      ((CategoryTheory.evaluation _ _).obj U ⋙ MonoidalCategory.tensorRight (N.obj.obj U))
    infer_instance
  have hlim : PreservesFiniteLimits (MonoidalCategory.tensorRight N) :=
    preservesFiniteLimits_of_natIso (Sheaf.tensorRightIso N).symm
  let : MonoidalClosed (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) :=
    Monoidal.Reflective.monoidalClosed
      (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} k))
  exact ⟨hlim, inferInstance⟩

/-- Tensor with a degree-zero sheaf over a field preserves a cohomological interval.
Source: Bhatt--Scholze, Remark 6.3.2; exact tensor over a field
(auxiliary; not a blueprint node).
Proof: presheaf tensor is pointwise exact over the field. Sheaf tensor is this tensor
followed by exact sheafification, and is also a left adjoint. The resulting exact
functor commutes with homology, giving the asserted vanishing for every complex. -/
theorem sfbFieldTensor_bounds (X : Scheme.{u}) (k : Type (u + 1)) [Field k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (a b : ℤ) (h : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) :
    ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) (q : ℤ),
      (q < a ∨ b < q) → IsZero ((sfbEtaleTensorDegreeZero X k C N).homology q) := by
  intro N q hq
  let := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
  have := (sfbFieldTensor_exact X k N).1
  have := (sfbFieldTensor_exact X k N).2
  let F := MonoidalCategory.tensorRight N
  exact (F.map_isZero (h q hq)).of_iso
    ((F.mapHomologicalComplexHomologyIso (.up ℤ) q).app C)

end AlgebraicGeometry.Scheme
