import Langlands.Analysis.DistributionFamilyIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral

/-! # Translation-covariant distributions on a real vector space -/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Test" => 𝓓((⊤ : Opens E), ℂ)

/-- A distribution that transforms by `χ z` under the pullback `x ↦ x + z`. -/
def TranslationCovariant (χ : E → ℂ) (T : Test →L[ℂ] ℂ) : Prop :=
  ∀ (z : E) (f g : Test), (∀ x, g x = f (x + z)) → T g = χ z * T f

private theorem smoothCompactFamily_of_joint {F : E → E → ℂ}
    (hF : ContDiff ℝ ∞ (fun p : E × E => F p.1 p.2))
    (S : Set E) (hS : IsCompact S) (hzero : ∀ z ∉ S, ∀ x, F z x = 0) :
    SmoothCompactFamily F := by
  refine ⟨fun z => hF.comp (contDiff_const.prodMk contDiff_id), fun i => ?_, ⟨S, hS, hzero⟩⟩
  let l := ContinuousLinearMap.inr ℝ E E
  let L : (E × E [×i]→L[ℝ] ℂ) →L[ℝ] (E [×i]→L[ℝ] ℂ) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => l)
  have hEq (z : E × E) : iteratedFDeriv ℝ i (F z.1) z.2 =
      L (iteratedFDeriv ℝ i (fun p : E × E => F p.1 p.2) z) := by
    let G : E × E → ℂ := fun p => F ((z.1, 0) + p).1 ((z.1, 0) + p).2
    have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add contDiff_id)
    have he : F z.1 = G ∘ l := by
      funext x
      simp [G, l]
    rw [he, l.iteratedFDeriv_comp_right hG _ (by simp),
      show iteratedFDeriv ℝ i G (l z.2) =
        iteratedFDeriv ℝ i (fun p : E × E => F p.1 p.2) ((z.1, 0) + l z.2) from
          iteratedFDeriv_comp_add_left (f := fun p : E × E => F p.1 p.2) i (z.1, 0) (l z.2)]
    simp [l, L]
  simp only [hEq]
  exact L.continuous.comp (hF.continuous_iteratedFDeriv (m := i) (by simp))

private def compactTest (K : Compacts E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hK : ∀ x ∉ K, f x = 0) : Test :=
  TestFunction.ofSupportedIn (K := K) (subset_univ _)
    (ContDiffMapSupportedIn.of_support_subset hf (fun x hx => by
      by_contra h
      exact hx (hK x h)))

section Haar

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem exists_proportional_integral (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hχ₀ : χ 0 = 1) (hχadd : ∀ x y, χ (x + y) = χ x * χ y)
    (T : Test →L[ℂ] ℂ) (hT : TranslationCovariant χ T) :
    ∃ c : ℂ, ∀ f : Test, T f = c * ∫ x, f x * χ (-x) ∂μ := by
  let ρ : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let ρC : E → ℂ := fun x => (ρ x : ℂ)
  have hρ : ContDiff ℝ ∞ ρC := Complex.ofRealCLM.contDiff.comp ρ.contDiff
  have eρ : tsupport ρC = tsupport ρ := by
    apply congrArg closure
    ext x
    simp [Function.mem_support, ρC]
  let L : Compacts E := ⟨tsupport ρC, eρ ▸ ρ.hasCompactSupport⟩
  have hρ0 (x : E) (hx : x ∉ L) : ρC x = 0 := image_eq_zero_of_notMem_tsupport hx
  let cut : Test := compactTest L (hρ.mul hχ) (fun x hx => by rw [hρ0 x hx, zero_mul])
  let d := ∫ x, ρC x ∂μ
  have hd : d ≠ 0 := by
    change (∫ x, (ρ x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    refine Complex.ofReal_ne_zero.mpr
      (ρ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        ρ.hasCompactSupport (fun _ => ρ.nonneg) (x := 0) ?_).ne'
    rw [ρ.one_of_mem_closedBall (Metric.mem_closedBall_self ρ.rIn_pos.le)]
    exact one_ne_zero
  refine ⟨T cut / d, fun f => ?_⟩
  let K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
  have hf0 (x : E) (hx : x ∉ K) : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  let S := (fun y : E × E => y.1 - y.2) '' ((K : Set E) ×ˢ (L : Set E))
  have hS : IsCompact S := (K.isCompact.prod L.isCompact).image (continuous_fst.sub continuous_snd)
  let Φ : E → E → ℂ := fun z x => f x * ρC (x - z)
  let Ψ : E → E → ℂ := fun z x => ρC x * (χ (-z) * f (x + z))
  have hΦjoint : ContDiff ℝ ∞ (fun q : E × E => Φ q.1 q.2) :=
    (f.contDiff.comp contDiff_snd).mul (hρ.comp (contDiff_snd.sub contDiff_fst))
  have hΨjoint : ContDiff ℝ ∞ (fun q : E × E => Ψ q.1 q.2) :=
    (hρ.comp contDiff_snd).mul ((hχ.comp contDiff_fst.neg).mul
      (f.contDiff.comp (contDiff_snd.add contDiff_fst)))
  have hΦ : SmoothCompactFamily Φ := smoothCompactFamily_of_joint hΦjoint S hS (by
    intro z hz x
    by_cases hx : x ∈ K
    · have hxz : x - z ∉ L := by
        intro h
        exact hz ⟨(x, x - z), ⟨hx, h⟩, by simp⟩
      simp [Φ, hρ0 _ hxz]
    · simp [Φ, hf0 _ hx])
  have hΨ : SmoothCompactFamily Ψ := smoothCompactFamily_of_joint hΨjoint S hS (by
    intro z hz x
    by_cases hx : x ∈ L
    · have hxz : x + z ∉ K := by
        intro h
        exact hz ⟨(x + z, x), ⟨h, hx⟩, by simp [add_comm]⟩
      simp [Ψ, hf0 _ hxz]
    · simp [Ψ, hρ0 _ hx])
  have hΦ0 (z : E) (x : E) (hx : x ∉ K) : Φ z x = 0 := by simp [Φ, hf0 _ hx]
  have hΨ0 (z : E) (x : E) (hx : x ∉ L) : Ψ z x = 0 := by simp [Ψ, hρ0 _ hx]
  let p (z : E) := compactTest K (hΦ.contDiff z) (hΦ0 z)
  let q (z : E) := compactTest L (hΨ.contDiff z) (hΨ0 z)
  let A := ∫ x, f x * χ (-x) ∂μ
  have hΦint (x : E) : (d • f) x = ∫ z, Φ z x ∂μ := by
    change d * f x = ∫ z, f x * ρC (x - z) ∂μ
    rw [integral_const_mul]
    have hneg : (∫ z, ρC (x - z) ∂μ) = ∫ z, ρC (x + z) ∂μ := by
      simpa only [sub_eq_add_neg] using integral_neg_eq_self (fun z => ρC (x + z)) μ
    rw [hneg, integral_add_left_eq_self]
    exact mul_comm _ _
  have hΨint (x : E) : (A • cut) x = ∫ z, Ψ z x ∂μ := by
    change A * (ρC x * χ x) = ∫ z, ρC x * (χ (-z) * f (x + z)) ∂μ
    rw [integral_const_mul]
    have htr : (∫ z, χ (-z) * f (x + z) ∂μ) = ∫ z, χ (x - z) * f z ∂μ := by
      rw [← integral_add_left_eq_self (fun z => χ (x - z) * f z) x]
      apply integral_congr_ae
      refine ae_of_all _ fun z => ?_
      change χ (-z) * f (x + z) = χ (x - (x + z)) * f (x + z)
      rw [show x - (x + z) = -z by abel]
    rw [htr]
    simp_rw [sub_eq_add_neg, hχadd, mul_assoc, mul_comm (χ (-_))]
    rw [integral_const_mul]
    change A * (ρC x * χ x) = ρC x * (χ x * A)
    ring
  have heq (z : E) : T (p z) = T (q z) := by
    let w := compactTest L
      (hρ.mul (f.contDiff.comp (contDiff_id.add contDiff_const)))
      (fun x hx => show ρC x * f (x + z) = 0 by rw [hρ0 _ hx, zero_mul])
    have hw : ∀ x, w x = p z (x + z) := by
      intro x
      change ρC x * f (x + z) = f (x + z) * ρC (x + z - z)
      rw [add_sub_cancel_right, mul_comm]
    have hq : q z = χ (-z) • w := TestFunction.ext fun x => by
      change ρC x * (χ (-z) * f (x + z)) = χ (-z) * (ρC x * f (x + z))
      ring
    have hχinv : χ (-z) * χ z = 1 := by rw [← hχadd, neg_add_cancel, hχ₀]
    rw [hq, map_smul, smul_eq_mul, hT z (p z) w hw, ← mul_assoc, hχinv, one_mul]
  have h := map_integral_family (μ := μ) T hΦ (K := K) (subset_univ _) hΦ0 p
    (fun _ _ => rfl) (d • f) hΦint
  have h' := map_integral_family (μ := μ) T hΨ (K := L) (subset_univ _) hΨ0 q
    (fun _ _ => rfl) (A • cut) hΨint
  rw [show (fun z => T (p z)) = (fun z => T (q z)) from funext heq, ← h',
    map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  apply mul_left_cancel₀ hd
  rw [h]
  field_simp
  ring

end Haar

variable [MeasurableSpace E]

/-- A continuous test functional transforming by a smooth additive character is a scalar
multiple of the corresponding negative-character integral. -/
def TranslationCovariantDistributionStatement (μ : Measure E) : Prop :=
  ∀ [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure],
    ∀ (χ : E → ℂ), ContDiff ℝ ∞ χ → χ 0 = 1 → (∀ x y, χ (x + y) = χ x * χ y) →
      ∀ T : Test →L[ℂ] ℂ, TranslationCovariant χ T →
        ∃ c : ℂ, ∀ f : Test, T f = c * ∫ x, f x * χ (-x) ∂μ

theorem translationCovariantDistribution (μ : Measure E) : TranslationCovariantDistributionStatement μ := by
  intro _ _ _ χ hχ hχ₀ hχadd T hT
  exact exists_proportional_integral μ χ hχ hχ₀ hχadd T hT

end Langlands.Analysis
