import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.Representation.Unitary.CharacterPositivity

/-! # Bounds and conjugation for Hecke eigenvalues in a unitarizable action -/

noncomputable section

namespace Langlands

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

/-- On any nonzero eigenvector for an integrated Hecke test, the scalar is
bounded by the `L¹` norm of the test when the representation has an invariant
positive form. If inversion preserves Haar measure and the adjoint test acts
on the same vector by a scalar, that scalar is the complex conjugate. -/
def IntegratedHeckeScalarControlStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (_b : InvariantPositiveForm ρ)
    (f : SchwartzBruhat G) {v : V}, v ≠ 0 →
    ∀ {c : ℂ}, Hecke.integratedAction μ ρ hρ f v = c • v →
    ‖c‖ ≤ ∫ g, ‖f g‖ ∂μ ∧
      ∀ [IsInvInvariant μ] {d : ℂ},
        Hecke.integratedAction μ ρ hρ (Hecke.TestFunction.adjoint f) v = d • v →
        d = starRingEnd ℂ c

/-- The matrix coefficient of the eigenvector computes the scalar by integration.
The invariant form bounds this coefficient and identifies the adjoint action. -/
theorem integratedHeckeScalarControl : IntegratedHeckeScalarControlStatement.{uG, uV} := by
  intro G _ _ _ _ _ V _ _ μ _ ρ hρ b f v hv c hc
  let _ : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ b.toInnerProductCore
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore b.toInnerProductCore.toCore
  constructor
  · have hval : inner ℂ v (c • v) = ∫ g, f g * inner ℂ v (ρ g v) ∂μ := by
      rw [← hc]
      exact Hecke.integratedAction_dual μ ρ hρ f v (b.rightFunctional v)
    have hisom (g : G) : ‖ρ g v‖ = ‖v‖ := by
      change Real.sqrt (b.inner (ρ g v) (ρ g v)).re = Real.sqrt (b.inner v v).re
      rw [b.invariant]
    have hpos : 0 < ‖v‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hv)
    refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖c‖ * (‖v‖ * ‖v‖) = ‖inner ℂ v (c • v)‖ := by
        rw [inner_smul_right, norm_mul, ← inner_self_re_eq_norm,
          ← norm_sq_eq_re_inner, pow_two]
      _ = ‖∫ g, f g * inner ℂ v (ρ g v) ∂μ‖ := congrArg norm hval
      _ ≤ ∫ g, ‖f g‖ * (‖v‖ * ‖v‖) ∂μ :=
        norm_integral_le_of_norm_le ((f.integrable μ).norm.mul_const _)
          (Filter.Eventually.of_forall fun g => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm v (ρ g v)).trans_eq
              (congrArg (‖v‖ * ·) (hisom g))) (norm_nonneg _))
      _ = (∫ g, ‖f g‖ ∂μ) * (‖v‖ * ‖v‖) := integral_mul_const _ _
  · intro _ d hd
    have heq : inner ℂ (d • v) v = inner ℂ v (c • v) := by
      rw [← hd, ← hc]
      exact b.integratedAction_adjoint μ hρ f v v
    rw [inner_smul_left, inner_smul_right] at heq
    have hconj : starRingEnd ℂ d = c :=
      mul_right_cancel₀ (inner_self_ne_zero.mpr hv) heq
    exact (Complex.conj_conj d).symm.trans (congrArg (starRingEnd ℂ) hconj)

end Langlands
