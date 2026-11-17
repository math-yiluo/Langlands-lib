import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceStatement
import Langlands.AlgebraicGeometry.Picard.NonzeroEndomorphismMixedEulerPositiveStatement
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityReduction
import Langlands.AlgebraicGeometry.Picard.RosatiZeroDimension
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange
import Langlands.AbelianScheme.Tate.TwoPowerTorsionDensityReduction

/-! # Integral Rosati positivity from the actual mixed Euler trace formula -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme.Rosati

open Langlands.AlgebraicGeometry.Picard

/-- The numerical reduction from the two geometric mixed Euler statements to
integral Rosati positivity for an actual ample Mumford presentation. -/
def MumfordMixedEulerPositivityReductionStatement : Prop :=
  MumfordMixedEulerTraceStatement.{u} →
  NonzeroEndomorphismMixedEulerPositiveStatement.{u} →
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [HasRationalInverse P W lam],
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (groupHom lam).hom.hom →
    IntegralDiagonalPositive A P W hadd lam

/-- The actual trace formula and mixed coefficient positivity imply integral
diagonal positivity for every supplied ample Mumford presentation. -/
theorem integralDiagonalPositive_of_ampleMumfordPresentation :
    MumfordMixedEulerPositivityReductionStatement.{u} := by
  intro hformula hmixed P k _ _ _ A W hadd lam _ hpres f hf
  obtain ⟨g, hg⟩ := Tate.exists_hasRelativeDimension A
  cases g with
  | zero =>
      exact (hf (hom_eq_zero_of_relativeDimension_zero hg f)).elim
  | succ d =>
      obtain ⟨L, B, evaluationB, M, evaluation, hL, heq⟩ := hpres
      have htop := lineBundleEulerPolynomial_topCoeff_pos
        A.X.hom (d + 1) hg inferInstance L hL
      have hpos := hmixed k A (d + 1) (Nat.succ_pos d) hg L hL f hf
      have htrace := hformula P k A W hadd lam (d + 1) (Nat.succ_pos d) hg
        L B evaluationB M evaluation hL heq f
      have hproduct :
          0 < traceForm P W hadd lam (homToHom0 f) (homToHom0 f) *
            (lineBundleEulerPolynomial A.X.hom L (d + 1)).coeff (d + 1) := by
        rw [htrace]
        exact mul_pos (by norm_num) hpos
      exact pos_of_mul_pos_left hproduct htop.le

end Langlands.AbelianScheme.Rosati
