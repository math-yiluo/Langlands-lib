import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.KrullDimension

/-! # Native finite-flat rank in top Euler polynomial coefficients -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Native finite-flat rank compares the coefficients at the target dimension
bound of polynomials representing the actual line-bundle Euler sequences. -/
def FiniteFlatEulerPolynomialCoefficientStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Scheme.{u})
    (s : Y ⟶ Spec (CommRingCat.of K)),
    IsProper s → IsNoetherian Y → Y.IsSeparated → IsIntegral Y →
    ∀ (f : X ⟶ Y), IsFinite f → Flat f →
    ∀ (d : ℕ), topologicalKrullDim Y ≤ d →
    ∀ (L : LineBundle Y)
      (hL : ∀ n, HasFiniteCohomology s (Langlands.Scheme.Modules.tensorPow L.obj n))
      (hF : ∀ n, HasFiniteCohomology (f ≫ s)
        (Langlands.Scheme.Modules.tensorPow ((Scheme.Modules.pullback f).obj L.obj) n))
      (P Q : Polynomial ℚ),
      (∀ n : ℕ, P.eval (n : ℚ) = (eulerCharacteristic s
        (Langlands.Scheme.Modules.tensorPow L.obj n) (hL n) : ℚ)) →
      (∀ n : ℕ, Q.eval (n : ℚ) = (eulerCharacteristic (f ≫ s)
        (Langlands.Scheme.Modules.tensorPow ((Scheme.Modules.pullback f).obj L.obj) n)
          (hF n) : ℚ)) →
      ∀ x : Y, Q.coeff d = (f.finrank x : ℚ) * P.coeff d

end Langlands.AlgebraicGeometry.Picard
