import Langlands.AlgebraicGeometry.Picard.Rosati
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Rational invertibility of an actual geometric polarization -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

/-- An actual geometric polarization has an inverse in the existing rational
category; no inverse or global kernel annihilator is an added premise. -/
def RationalInverseStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam → HasRationalInverse P W lam

end Langlands.AbelianScheme.Rosati
