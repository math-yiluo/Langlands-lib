import Langlands.AlgebraicGeometry.Modules.AmpleCoherentEulerCoefficientStatement

/-! # Integral ample Euler coefficient positivity from lower dimension -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The coefficient criterion in dimension `d` implies positivity of the
structure-module Euler coefficient on an integral scheme of dimension `d + 1`. -/
def IntegralAmpleEulerCoefficientStatement : Prop :=
  ∀ (d : ℕ), AmpleCoherentEulerCoefficientInDimension.{u} d →
    ∀ (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
      [IsNoetherian X] [X.IsSeparated]
      (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
      (L : Picard.LineBundle X), L.IsAmple →
      topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) →
        0 < (Picard.lineBundleEulerPolynomial f L (d + 1)).coeff (d + 1)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
