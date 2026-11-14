import Langlands.AlgebraicGeometry.Picard.Rosati
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Positivity of the actual geometric Rosati trace form -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

/-- Milne's positive-definite symmetric trace form, on the actual rational
endomorphisms and fixed geometric trace. No trace comparison, finite dimension
or positivity premise is added. This is a proof target. -/
def PositivityStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam →
    ∀ [HasRationalInverse P W lam],
      (∀ a b : End0 A, traceForm P W hadd lam a b = traceForm P W hadd lam b a) ∧
      (∀ a : End0 A, 0 ≤ traceForm P W hadd lam a a) ∧
      ∀ a : End0 A, a ≠ 0 →
        0 < geometricEndomorphismTrace A (a * involution P W hadd lam a)

end Langlands.AbelianScheme.Rosati
