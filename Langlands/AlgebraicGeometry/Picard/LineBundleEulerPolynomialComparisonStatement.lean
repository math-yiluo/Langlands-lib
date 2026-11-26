import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler

/-! # Eventual square comparison for twisted Euler polynomials -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter

universe u

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Eventual agreement of squared twisted Euler characteristics determines the
twisted Euler polynomial for ample twisting bundles on smooth proper geometrically
connected schemes of the same relative dimension. -/
def CoherentEulerPolynomialSquareComparisonStatement : Prop :=
  ∀ {K K' : Type u} [Field K] [Field K'] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (p' : X' ⟶ Spec (.of K')) [IsProper p] [IsProper p']
    (g : ℕ), SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g p' →
    GeometricallyConnected p → GeometricallyConnected p' →
    ∀ (L N : LineBundle X) (L' N' : LineBundle X'), L.IsAmple → L'.IsAmple →
      (∀ᶠ n : ℕ in atTop,
        coherentEulerSequence p N.obj (hasFiniteAffineSections_lineBundle N) L n ^ 2 =
          coherentEulerSequence p' N'.obj (hasFiniteAffineSections_lineBundle N') L' n ^ 2) →
      coherentEulerPolynomial p N.obj (hasFiniteAffineSections_lineBundle N) L g =
        coherentEulerPolynomial p' N'.obj (hasFiniteAffineSections_lineBundle N') L' g

end Langlands.AlgebraicGeometry.Picard
