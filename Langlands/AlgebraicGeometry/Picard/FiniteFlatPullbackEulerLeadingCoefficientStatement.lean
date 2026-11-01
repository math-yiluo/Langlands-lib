import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialStatement
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Leading Euler coefficients under actual finite flat pullback -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Actual finite flat pullback multiplies the leading coefficient of an ample
line-bundle Euler polynomial by the native rank at every target point. -/
def FiniteFlatPullbackEulerLeadingCoefficientStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (X : Over (Spec (CommRingCat.of K))) (g : ℕ),
    SmoothOfRelativeDimension g X.hom →
      IsProper X.hom → GeometricallyConnected X.hom →
        ∀ (f : X ⟶ X), IsFinite f.left → Flat f.left →
          ∀ (L : LineBundle X.left), L.IsAmple →
            ∀ (hL : ∀ n : ℕ, HasFiniteCohomology X.hom
                (Langlands.Scheme.Modules.tensorPow L.obj n))
              (hF : ∀ n : ℕ, HasFiniteCohomology X.hom
                (Langlands.Scheme.Modules.tensorPow
                  ((Scheme.Modules.pullback f.left).obj L.obj) n))
              (P Q : Polynomial ℚ),
              (∀ n : ℕ, P.eval (n : ℚ) =
                (eulerCharacteristic X.hom
                  (Langlands.Scheme.Modules.tensorPow L.obj n) (hL n) : ℚ)) →
              (∀ n : ℕ, Q.eval (n : ℚ) =
                (eulerCharacteristic X.hom
                  (Langlands.Scheme.Modules.tensorPow
                    ((Scheme.Modules.pullback f.left).obj L.obj) n) (hF n) : ℚ)) →
              ∀ x : X.left,
                Q.leadingCoeff = (f.left.finrank x : ℚ) * P.leadingCoeff

end Langlands.AlgebraicGeometry.Picard
