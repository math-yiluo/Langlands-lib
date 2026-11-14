import Langlands.AlgebraicGeometry.Picard.Rosati
import Langlands.AbelianScheme.Tate.WeilHom0Pullback
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Positive multiplier of an actual rational polarized self-isogeny -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

/-- The existing actual dual-pullback equation has positive rational-unit
multiplier for a rational self-isogeny when the actual identity is nonzero.
No Rosati positivity or inverse-existence premise is added. -/
def MultiplierPositivityStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam →
    id0 A ≠ 0 →
    ∀ (e : (rationalization _).obj A ≅ (rationalization _).obj A) (q : ℚˣ),
      IsRationalDualPullbackMultiple P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability
        W.hasDual W.hasDual W.geometry W.geometry
        W.inversePoincare W.evaluation W.inversePoincare W.evaluation
        hadd (q : ℚ) e.hom (homToHom0 lam) (homToHom0 lam) →
      0 < (q : ℚ)

end Langlands.AbelianScheme.Rosati
