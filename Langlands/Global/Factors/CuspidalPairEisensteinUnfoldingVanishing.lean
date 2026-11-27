import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingGroups
import Langlands.Global.RankinSelberg.UnfoldingMeasure

/-! # Vanishing of the non-open cells

An abstract vanishing criterion for integrals over a fundamental domain of a countable subgroup
`Λ ≤ N ≤ H`. Let `H` carry a left invariant s-finite measure, and let `N` carry an s-finite
measure that is left, right and inversion invariant and gives finite positive mass to a
measurable strict fundamental domain of `Λ` in `N`. Let `Φ : H → ℂ` be measurable, left
`Λ`-invariant and integrable on a measurable strict fundamental domain `sH` of `Λ` in `H`. If
right translation by one element `v₀` of `N` multiplies every function `n ↦ Φ(n x)` on `N` by
the same constant `c ≠ 1`, that is `Φ(n v₀ x) = c Φ(n x)`, then `Φ` has integral zero on `sH`.
The proof is Weil averaging over `Λ \ N`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal.Unfolding

section Abstract

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {N : Subgroup H} (Λ : Subgroup N) [Countable Λ]
  (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
  (ν : Measure N) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] [ν.IsInvInvariant] [SFinite ν]

omit [ν.IsInvInvariant] in
/-- Right translation by `v₀` permutes the fundamental domains of `Λ` in `N`: integrals of left
`Λ`-invariant functions are unchanged. -/
theorem setIntegral_mul_right_eq {sN : Set N} (hsNm : MeasurableSet sN)
    (hsN : ∀ n : N, ∃! l : Λ, (l : N) * n ∈ sN) (v₀ : N) {G : N → ℂ}
    (hG : ∀ (l : Λ) (n : N), G ((l : N) * n) = G n) :
    ∫ n in sN, G (n * v₀) ∂ν = ∫ n in sN, G n ∂ν := by
  have hemb : MeasurableEmbedding (fun n : N => n * v₀) := measurableEmbedding_mulRight v₀
  have h1 := (measurePreserving_mul_right ν v₀).setIntegral_image_emb hemb G sN
  rw [← h1]
  have hfd : IsFundamentalDomain Λ sN ν :=
    IsFundamentalDomain.mk' hsNm.nullMeasurableSet (fun n => by
      simpa [Subgroup.smul_def] using hsN n)
  have hfd' : IsFundamentalDomain Λ ((fun n : N => n * v₀) '' sN) ν := by
    refine IsFundamentalDomain.mk' (hemb.measurableSet_image.mpr hsNm).nullMeasurableSet
      (fun n => ?_)
    obtain ⟨l, hl, hu⟩ := hsN (n * v₀⁻¹)
    refine ⟨l, ?_, fun l' hl' => hu l' ?_⟩
    · refine ⟨(l : N) * (n * v₀⁻¹), hl, ?_⟩
      simp [Subgroup.smul_def, mul_assoc]
    · obtain ⟨m, hm, hmeq⟩ := hl'
      have : (l' : N) * (n * v₀⁻¹) = m := by
        rw [← mul_assoc]
        change (l' • n : N) * v₀⁻¹ = m
        rw [← hmeq]
        simp
      rw [this]
      exact hm
  exact hfd'.setIntegral_eq hfd (fun l n => by simpa [Subgroup.smul_def] using hG l n)

/-- **Vanishing by Weil averaging.** -/
theorem setIntegral_eq_zero_of_mul_right
    {sH : Set H} (hsHm : MeasurableSet sH) (hsH : ∀ x : H, ∃! l : Λ, ((l : N) : H) * x ∈ sH)
    {sN : Set N} (hsNm : MeasurableSet sN) (hsN : ∀ n : N, ∃! l : Λ, (l : N) * n ∈ sN)
    (hν0 : ν sN ≠ 0) (hνfin : ν sN ≠ ∞)
    {Φ : H → ℂ} (hΦ : Measurable Φ) (hΦΛ : ∀ (l : Λ) (x : H), Φ (((l : N) : H) * x) = Φ x)
    (hint : IntegrableOn Φ sH μ) (v₀ : N) (c : ℂ) (hc : c ≠ 1)
    (hv₀ : ∀ (n : N) (x : H), Φ ((n : H) * (v₀ : H) * x) = c * Φ ((n : H) * x)) :
    ∫ x in sH, Φ x ∂μ = 0 := by
  obtain ⟨hI, hEq⟩ := integrable_and_integral_average Λ μ ν hsHm hsH hsNm hsN hνfin hΦ hΦΛ hint
  have hinner : ∀ x : H, ∫ n in sN, Φ ((n : H) * x) ∂ν = 0 := by
    intro x
    have hG : ∀ (l : Λ) (n : N), Φ ((((l : N) * n : N) : H) * x) = Φ ((n : H) * x) := by
      intro l n
      rw [Subgroup.coe_mul, mul_assoc, hΦΛ]
    have h1 := setIntegral_mul_right_eq Λ ν hsNm hsN v₀ (G := fun n : N => Φ ((n : H) * x)) hG
    have h2 : ∫ n in sN, Φ (((n * v₀ : N) : H) * x) ∂ν = c * ∫ n in sN, Φ ((n : H) * x) ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext n
      rw [Subgroup.coe_mul, hv₀]
    rw [h2] at h1
    have h3 : (c - 1) * ∫ n in sN, Φ ((n : H) * x) ∂ν = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc)
  have hfub : ∫ p, Φ ((p.1 : H) * p.2) ∂((ν.restrict sN).prod (μ.restrict sH)) =
      ∫ x in sH, ∫ n in sN, Φ ((n : H) * x) ∂ν ∂μ :=
    integral_prod_symm (fun p : N × H => Φ ((p.1 : H) * p.2)) hI
  rw [hfub] at hEq
  simp_rw [hinner, integral_zero] at hEq
  have hne : (ν sN).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hν0, hνfin⟩
  exact (smul_eq_zero.mp hEq.symm).resolve_left hne

end Abstract

end Langlands.Global.CuspidalPairEisenstein.Unfolding
