import Langlands.AlgebraicGeometry.Picard.Rosati
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Algebra laws of the actual rational Rosati operation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

/-- The actual conjugation by a geometric polarization is a rational-linear
algebra anti-involution. Rational invertibility is its construction prerequisite,
asserted unconditionally for polarizations by RationalInverseStatement. -/
def AlgebraLawsStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam →
    ∀ [HasRationalInverse P W lam],
      (∀ a b : End0 A,
        involution P W hadd lam (a + b) =
          involution P W hadd lam a + involution P W hadd lam b) ∧
      (∀ (q : ℚ) (a : End0 A),
        involution P W hadd lam (q • a) = q • involution P W hadd lam a) ∧
      (∀ a b : End0 A,
        involution P W hadd lam (a * b) =
          involution P W hadd lam b * involution P W hadd lam a) ∧
      (∀ q : ℚ,
        involution P W hadd lam (algebraMap ℚ (End0 A) q) =
          algebraMap ℚ (End0 A) q) ∧
      ∀ a : End0 A,
        involution P W hadd lam (involution P W hadd lam a) = a

end Langlands.AbelianScheme.Rosati
