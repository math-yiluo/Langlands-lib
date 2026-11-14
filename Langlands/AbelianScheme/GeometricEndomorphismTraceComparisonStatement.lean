import Langlands.AbelianScheme.GeometricEndomorphismTrace
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Comparison with the geometric endomorphism trace -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The actual prime Tate modules are finite dimensional, with their geometric
rank, and the fixed rational trace agrees with every actual prime Tate trace.
In particular its defining rational lift exists. This is a proof target. -/
def GeometricEndomorphismTraceComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime],
    FiniteDimensional ℚ_[p] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p) ∧
      (∀ g : ℕ, A.HasRelativeDimension g →
        Module.finrank ℚ_[p] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p) = 2 * g) ∧
      ∀ a : End0 A,
        algebraMap ℚ ℚ_[p] (geometricEndomorphismTrace A a) =
          primeEndomorphismTrace A p a

end Langlands.AbelianScheme
