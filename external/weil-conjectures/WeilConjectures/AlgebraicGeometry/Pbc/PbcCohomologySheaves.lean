/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Cohomology sheaves and geometric fibres at a PBC coefficient stage

The cohomology is the recorded Mathlib homology functor. Rationalization changes
its Hom groups, not its integral representative. Fibres use completed geometric
pullback and exact point sections before extension to the algebraic closure.

## References

* Bhatt--Scholze, Section 6.8
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (X : Scheme.{u})

variable [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

end AlgebraicGeometry.Scheme
