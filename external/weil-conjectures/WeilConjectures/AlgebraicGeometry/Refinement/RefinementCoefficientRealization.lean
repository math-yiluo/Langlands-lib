/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The finite coefficient realization interface for refinement comparisons

The recorded finite-module definitions are reexported. This exposes coefficient realization
without importing the second copy of the fixed-coefficient six-functor declarations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical associated-module-sheaf realization is fully faithful and every module
sheaf is in its essential image. This identifies fixed scalar module sheaves with the
modules over the specified continuous-function coefficient sheaf, not a new coefficient
category. -/
theorem finiteCoefficientRealization_full_faithful_essSurj (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).Full ∧
      (finiteCoefficientRealization T Λ).Faithful ∧
        (finiteCoefficientRealization T Λ).EssSurj := by
  let := finiteCoefficientRealizationIsEquivalenceRing T Λ
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Realization gives the coefficient equivalence used for canonical transport. -/
instance refinementRealizationIsEquivalence (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientRealization T Λ).IsEquivalence where
  full := (finiteCoefficientRealization_full_faithful_essSurj T Λ).1
  faithful := (finiteCoefficientRealization_full_faithful_essSurj T Λ).2.1
  essSurj := (finiteCoefficientRealization_full_faithful_essSurj T Λ).2.2

end AlgebraicGeometry.ProEtale
