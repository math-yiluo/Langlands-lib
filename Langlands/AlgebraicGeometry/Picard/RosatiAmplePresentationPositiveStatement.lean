import Langlands.AlgebraicGeometry.Picard.RosatiPositivityReduction
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Integral Rosati positivity for an actual ample Mumford presentation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati

/-- The numerical positivity obligation for the fixed Rosati form when the
polarization already has an ample Mumford presentation over its ground field.
This predicate does not assert that the obligation has been proved. -/
def AmplePresentationIntegralPositiveStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [hinv : HasRationalInverse P W lam],
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (groupHom lam).hom.hom →
    @IntegralDiagonalPositive k _ A P W hadd lam hinv

end Langlands.AbelianScheme.Rosati
