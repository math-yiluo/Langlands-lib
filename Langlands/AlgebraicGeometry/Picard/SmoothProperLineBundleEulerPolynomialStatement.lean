import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Rat.Cast.Order

/-! # Euler polynomials of actual line bundles on smooth proper schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The Euler characteristics of the actual tensor powers of a line bundle
are polynomial of degree at most the relative dimension. For an ample bundle
the degree is exact and the leading coefficient is positive. -/
def SmoothProperLineBundleEulerPolynomialStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (X : Over (Spec (CommRingCat.of K))) (g : ℕ),
    SmoothOfRelativeDimension g X.hom →
      IsProper X.hom → GeometricallyConnected X.hom →
        ∀ (L : LineBundle X.left),
          ∃ (h : ∀ n : ℕ,
              HasFiniteCohomology X.hom (Langlands.Scheme.Modules.tensorPow L.obj n)),
            ∃ P : Polynomial ℚ,
              (∀ n : ℕ, P.eval (n : ℚ) =
                (eulerCharacteristic X.hom
                  (Langlands.Scheme.Modules.tensorPow L.obj n) (h n) : ℚ)) ∧
              P.natDegree ≤ g ∧
              (L.IsAmple → P.natDegree = g ∧ 0 < P.leadingCoeff)

end Langlands.AlgebraicGeometry.Picard
