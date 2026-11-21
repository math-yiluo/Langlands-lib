import Langlands.Analysis.Local.QuotientIntegratedContinuousRepresentativeStatement
import Langlands.Analysis.Local.QuotientConvolutionKernelProof
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory Filter
open scoped CompactlySupported Pointwise

/-- Continuous representatives of compactly supported convolutions on a left
coset space. -/
theorem quotientIntegratedContinuousRepresentative :
    QuotientIntegratedContinuousRepresentativeStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ μH _ _ _ _ _ μG _ _ ν _ hν π hπnorm hπmeas hcompat
    f hf φ
  obtain ⟨v, hvc, hvφ, hvb⟩ := quotientConvolutionKernel H hH μH μG ν hν f
  have hmk : ∀ (h : H) (y : G), leftQuotientMap H (h.val * y) = leftQuotientMap H y := by
    intro h y
    apply Quotient.sound
    show (QuotientGroup.rightRel H) (h.val * y) y
    rw [QuotientGroup.rightRel_apply]
    simp [mul_inv_rev]
  have hinv : ∀ (h : H) (x : G), inner ℂ (v (h.val * x)) φ = inner ℂ (v x) φ := by
    intro h x
    rw [(hvφ _ φ).2, (hvφ x φ).2]
    congr 1
    funext a
    rw [mul_assoc, hmk]
  set ψ : LeftQuotient H → ℂ := descend H (fun x => inner ℂ (v x) φ) hinv with hψdef
  have hψmk : ∀ x, ψ (leftQuotientMap H x) = inner ℂ (v x) φ := fun x => rfl
  have hψc : Continuous ψ :=
    (hvc.inner continuous_const).quotient_lift _
  -- The pointwise representative of the integrated action.
  have hq := leftQuotient_isOpenQuotientMap H
  have : LocallyCompactSpace (LeftQuotient H) := leftQuotient_locallyCompactSpace H
  have : SecondCountableTopology (LeftQuotient H) :=
    TopologicalSpace.Quotient.secondCountableTopology hq.isOpenMap
  have hact : Continuous (fun p : LeftQuotient H × G => rightTranslate H p.2 p.1) := by
    have hpq : IsOpenQuotientMap (Prod.map (leftQuotientMap H) (id : G → G)) :=
      hq.prodMap IsOpenQuotientMap.id
    rw [← hpq.continuous_comp_iff]
    have : (fun p : LeftQuotient H × G => rightTranslate H p.2 p.1) ∘
        Prod.map (leftQuotientMap H) (id : G → G) =
        fun p : G × G => leftQuotientMap H (p.1 * p.2) := by
      funext p
      rfl
    rw [this]
    exact hq.continuous.comp (continuous_fst.mul continuous_snd)
  have hpt := Langlands.Analysis.integratedTranslationPointwise (LeftQuotient H) ν G μG
    (fun q a => rightTranslate H a q) hact.measurable (fun g => hν.right_invariant g)
    π hπnorm hπmeas hcompat f hf
  have heval : ∀ q : LeftQuotient H, ∫ a, f a * φ (rightTranslate H a q) ∂μG = ψ q := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      rw [show (Quotient.mk _ x : LeftQuotient H) = leftQuotientMap H x from rfl, hψmk,
        (hvφ x φ).2]
      rfl
  refine ⟨ψ, hψc, ?_, ?_⟩
  · filter_upwards [(hpt φ).2] with q hq'
    rw [hq', heval]
  · intro x M hM
    have h1 : ‖ψ (leftQuotientMap H x)‖ ≤ ‖v x‖ * ‖φ‖ := by
      rw [hψmk]
      exact norm_inner_le_norm _ _
    have h2 := hvb x M hM
    calc ‖ψ (leftQuotientMap H x)‖ ^ 2 ≤ (‖v x‖ * ‖φ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖v x‖ ^ 2 * ‖φ‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

end Langlands.QuotientIntegration
