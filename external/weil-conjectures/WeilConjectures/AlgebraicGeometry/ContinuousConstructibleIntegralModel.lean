/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralSingle
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Integral models of bounded constructible continuous coefficient complexes -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Every bounded constructible continuous E complex has a constructible integral model.
Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node).

Proof in words. On each stratum, locally finite presentations over the continuous E
coefficient sheaf become locally free after finite refinement. Lemma 6.8.13 gives a
constructible integral lattice for these finite-rank local systems; it does not require
a globally lisse integral lattice. Extension by zero gives integral models for their
locally closed extensions. The integral Hom localization theorem, proved using
bounded-below coproduct compactness, clears the finitely many denominators in the
extension classes. Induction through the bounded truncation triangles then constructs
an integral bounded constructible complex M and an isomorphism M[1/ℓ] ≅ K.
The continuous-function localization isomorphism on compact profinite tests identifies
M[1/ℓ] with the actual derived functor integralScalarExtension, after exact pullback
from the point. The empty scheme and zero complex use the zero integral complex. -/
theorem continuousConstructible_integral_model (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    ∃ M : integralConstructible ℓ E X,
      Nonempty ((integralScalarExtension ℓ E X).obj M.obj ≅ K.obj) := by
  let Q := ((ProEtale.boundedConstructible
    (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙ integralScalarExtension ℓ E X).essImage
  have : Q.IsTriangulated := continuousConstructible_integral_image_triangulated ℓ E X
  let P := ObjectProperty.isoClosure (fun F ↦ ProEtale.IsConstructibleModuleObject
    (condensedRingObj (Profinite.continuousMapRingObj E) X) F)
  have hP : ∀ F, P F → Q ((DerivedCategory.singleFunctor _ 0).obj F) := by
    rintro F ⟨G, hG, ⟨e⟩⟩
    exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
      (continuousConstructible_integral_single_model ℓ E X G hG)
  exact DerivedCategory.prop_of_bounded Q P hP K.obj K.property.1
    (fun n ↦ ⟨_, K.property.2 n, ⟨Iso.refl _⟩⟩)

end AlgebraicGeometry.ProEtale.CondensedRing
