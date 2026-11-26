import Langlands.Analysis.Complex.EntireStripIntegral
import Langlands.Analysis.MellinHalfPlaneProof
import Langlands.Analysis.LandauDirichlet
import Langlands.Global.RankinSelberg.ArchimedeanGammaBounds

/-! # Integrating entire normalized Mellin fibers -/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinMarginal

open Langlands.LocalFactor.Archimedean (HasStripExponentialGrowth)
open ArchimedeanInverseMellin (StripExpType rpow_le_add)
open Langlands.GeneralDirichlet (eqOn_halfPlane)

variable {P X Y : Type*} [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace Y]

private theorem mellin_right_differentiable {X₀ : Type*} [MeasurableSpace X₀] {μ : Measure X₀}
    {A : X₀ → ℂ} {δ : X₀ → ℝ} (hA : AEStronglyMeasurable A μ) (hδ : AEMeasurable δ μ)
    (hpos : ∀ x, 0 < δ x) (b : ℝ)
    (hI : ∀ r : ℝ, b < r → Integrable (fun x => A x * (δ x : ℂ) ^ (r : ℂ)) μ) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, A x * (δ x : ℂ) ^ s ∂μ) {s : ℂ | b < s.re} := by
  have h := Langlands.Analysis.mellinHalfPlane X₀ μ A δ (-b) hpos hA hδ (fun r hr => by
    simpa only [Complex.ofReal_neg, sub_neg_eq_add, Complex.ofReal_add] using hI (r + b) (by linarith))
  have h_aff : Differentiable ℂ (fun s : ℂ => s - (b : ℂ)) := differentiable_id.sub_const _
  have hmaps : MapsTo (fun s : ℂ => s - (b : ℂ)) {s : ℂ | b < s.re} {s : ℂ | 0 < s.re} := by
    intro z hz
    change 0 < (z - (b : ℂ)).re
    change b < z.re at hz
    simpa only [Complex.sub_re, Complex.ofReal_re, sub_pos] using hz
  simpa only [Function.comp_def, Complex.ofReal_neg, sub_neg_eq_add, sub_add_cancel] using
    h.comp h_aff.differentiableOn hmaps

private theorem norm_MellinKernel {X₀ : Type*} {A : X₀ → ℂ} {δ : X₀ → ℝ}
    (hδ : ∀ x, 0 < δ x) (s : ℂ) (x : X₀) :
    ‖A x * (δ x : ℂ) ^ s‖ = ‖A x‖ * δ x ^ s.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x)]

private theorem mellinKernel_integrable (μ : Measure X) (A : X → ℂ) (δ : X → ℝ)
    (hA : AEStronglyMeasurable A μ) (hδ : Measurable δ) (hpos : ∀ x, 0 < δ x)
    (s : ℂ) (hi : Integrable (fun x => ‖A x‖ * δ x ^ s.re) μ) :
    Integrable (fun x => A x * (δ x : ℂ) ^ s) μ :=
  hi.mono' (hA.mul ((Complex.continuous_ofReal.measurable.comp hδ).pow_const s).aestronglyMeasurable)
    (ae_of_all _ fun x => le_of_eq (norm_MellinKernel hpos s x))

private theorem mellin_fiber_integrals (η : Measure P) (μ : Measure X) [SFinite η] [SFinite μ]
    (A : P × X → ℂ) (δ : P × X → ℝ) (hA : AEStronglyMeasurable A (η.prod μ))
    (hδ : Measurable δ) (hpos : ∀ z, 0 < δ z) (b : ℝ)
    (hi : ∀ x : ℝ, b ≤ x → Integrable (fun z => ‖A z‖ * δ z ^ x) (η.prod μ)) :
    ∀ᵐ p ∂η, (∀ s : ℂ, b < s.re → Integrable (fun x => A (p, x) * (δ (p, x) : ℂ) ^ s) μ) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∫ x, A (p, x) * (δ (p, x) : ℂ) ^ s ∂μ) {s : ℂ | b < s.re} := by
  have hAll : ∀ᵐ p ∂η, ∀ j : ℕ, Integrable (fun x => ‖A (p, x)‖ * δ (p, x) ^ (b + j)) μ :=
    ae_all_iff.mpr fun j => (hi (b + j) (le_add_of_nonneg_right (Nat.cast_nonneg j))).prod_right_ae
  filter_upwards [hAll, hA.prodMk_left] with p hp hpA
  have hδ' : Measurable (fun x => δ (p, x)) := hδ.comp measurable_prodMk_left
  have hI (s : ℂ) (hs : b < s.re) : Integrable (fun x => A (p, x) * (δ (p, x) : ℂ) ^ s) μ := by
    obtain ⟨j, hj⟩ := exists_nat_ge (s.re - b)
    apply mellinKernel_integrable μ (fun x => A (p, x)) (fun x => δ (p, x)) hpA hδ' (fun x => hpos (p, x)) s
    have h₀ : Integrable (fun x => ‖A (p, x)‖ * δ (p, x) ^ b) μ := by simpa only [Nat.cast_zero, add_zero] using hp 0
    refine (h₀.add (hp j)).mono' (hpA.norm.mul (hδ'.pow_const s.re).aestronglyMeasurable) ?_
    exact ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg (A (p, x)))
        (Real.rpow_nonneg (hpos (p, x)).le _))]
      exact (mul_le_mul_of_nonneg_left (rpow_le_add (hpos (p, x)) hs.le (by linarith))
        (norm_nonneg _)).trans_eq (mul_add _ _ _)
  exact ⟨hI, mellin_right_differentiable hpA hδ'.aemeasurable (fun x => hpos (p, x)) b
    (fun s hs => hI (s : ℂ) (by rwa [Complex.ofReal_re]))⟩

private theorem strip_bound (L : ℂ → ℂ) (hL : StripExpType L) (b : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ, s.re = b → ‖L s‖ ≤ C * Real.exp (K * |s.im|) := by
  obtain ⟨C, K, hC, hK, h⟩ := hL b b
  refine ⟨C, K, hC, hK, fun s hs => ?_⟩
  have hRep : (b : ℂ) + s.im * Complex.I = s := by rw [← hs, Complex.re_add_im]
  simpa only [hRep] using h b le_rfl le_rfl s.im

private theorem bound_product (u : ℂ) (f : X → ℂ) (μ : Measure X) (C T : ℝ)
    (hu : ‖u‖ ≤ C * T) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    ‖u * (∫ x, f x ∂μ)‖ ≤ (C * ∫ x, ‖f x‖ ∂μ) * T := by
  rw [norm_mul, mul_right_comm]
  exact mul_le_mul hu (norm_integral_le_integral_norm f) (norm_nonneg _) (mul_nonneg hC hT)

/-- If both vertical ends of an entire fiber come from product Mellin integrals, absolute
moments of the product kernels control the integrated entire family. The endpoint formulas
may begin on a different right half-plane at each fiber. -/
def ArchimedeanMellinMarginalStatement : Prop :=
  ∀ (η : Measure P) (μ : Measure X) (ν : Measure Y) [SFinite η] [SFinite μ] [SFinite ν]
    (F : P × X → ℂ) (Fd : P × Y → ℂ) (δ : P × X → ℝ) (δd : P × Y → ℝ),
    AEStronglyMeasurable F (η.prod μ) → AEStronglyMeasurable Fd (η.prod ν) → Measurable δ → Measurable δd →
    (∀ z, 0 < δ z) → (∀ z, 0 < δd z) →
    ∀ (b : ℝ), (∀ x : ℝ, b ≤ x → Integrable (fun z => ‖F z‖ * δ z ^ x) (η.prod μ)) →
    (∀ x : ℝ, b ≤ x → Integrable (fun z => ‖Fd z‖ * δd z ^ x) (η.prod ν)) →
    ∀ (L Ld : ℂ → ℂ), Differentiable ℂ L → Differentiable ℂ Ld → StripExpType L → StripExpType Ld →
    ∀ (J : P → ℂ → ℂ), (∀ s, AEStronglyMeasurable (fun p => J p s) η) →
    (∀ᵐ p ∂η, Differentiable ℂ (J p) ∧ HasStripExponentialGrowth (J p)) →
    let K (s : ℂ) (z : P × X) := F z * (δ z : ℂ) ^ s
    let Kd (s : ℂ) (z : P × Y) := Fd z * (δd z : ℂ) ^ s
    (∀ᵐ p ∂η, ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      (Integrable (fun x => K s (p, x)) μ → L s * (∫ x, K s (p, x) ∂μ) = J p s) ∧
      (Integrable (fun x => Kd s (p, x)) ν → Ld s * (∫ x, Kd s (p, x) ∂ν) = J p (1 - s))) →
    (∀ s, Integrable (fun p => J p s) η) ∧ Differentiable ℂ (fun s => ∫ p, J p s ∂η) ∧
    ∀ s : ℂ, b < s.re → (∫ p, J p s ∂η) = L s * ∫ z, K s z ∂η.prod μ

set_option maxHeartbeats 1400000 in
theorem archimedeanMellinMarginal : ArchimedeanMellinMarginalStatement (P := P) (X := X) (Y := Y) := by
  intro η μ ν _ _ _ F Fd δ δd hF hFd hδ hδd hpos hposd b hi hid L Ld hL hLd hLt hLdt J hM hJ K Kd hEnd
  have ho := mellin_fiber_integrals η μ F δ hF hδ hpos b hi
  have hr := mellin_fiber_integrals η ν Fd δd hFd hδd hposd b hid
  have hE : ∀ᵐ p ∂η, ∀ s : ℂ, b < s.re →
      L s * (∫ x, K s (p, x) ∂μ) = J p s ∧ Ld s * (∫ x, Kd s (p, x) ∂ν) = J p (1 - s) := by
    filter_upwards [ho, hr, hJ, hEnd] with p hp hpd hJp hR
    obtain ⟨c, hc⟩ := hR
    have hO := eqOn_halfPlane ((hL.differentiableOn (s := {s : ℂ | b < s.re})).mul hp.2)
      hJp.1.differentiableOn (σ₁ := max b c) (fun s hs =>
        (hc s ((le_max_right _ _).trans_lt hs)).1 (hp.1 s ((le_max_left _ _).trans_lt hs)))
    have hRef : Differentiable ℂ (fun s : ℂ => J p (1 - s)) := hJp.1.comp (differentiable_id.const_sub 1)
    have hR := eqOn_halfPlane ((hLd.differentiableOn (s := {s : ℂ | b < s.re})).mul hpd.2)
      hRef.differentiableOn (σ₁ := max b c) (fun s hs =>
        (hc s ((le_max_right _ _).trans_lt hs)).2 (hpd.1 s ((le_max_left _ _).trans_lt hs)))
    exact fun s hs => ⟨hO hs, hR hs⟩
  have hI (s : ℂ) (hs : b < s.re) : Integrable (K s) (η.prod μ) :=
    mellinKernel_integrable (η.prod μ) F δ hF hδ hpos s (hi _ hs.le)
  have hLines (u v : ℝ) (_ : u ≤ v) : ∃ a c K₀ : ℝ, a < u ∧ v < c ∧
      ∃ B : P → ℝ, Integrable B η ∧ ∀ᵐ p ∂η, 0 ≤ B p ∧ ∀ s : ℂ, s.re = a ∨ s.re = c →
        ‖J p s‖ ≤ B p * Real.exp (K₀ * |s.im|) := by
    let a := min u (-b) - 1
    let c := max v b + 1
    have hau : a < u := by dsimp [a]; linarith [min_le_left u (-b)]
    have hvc : v < c := by dsimp [c]; linarith [le_max_left v b]
    have hab : b < 1 - a := by dsimp [a]; linarith [min_le_right u (-b)]
    have hcb : b < c := by dsimp [c]; linarith [le_max_right v b]
    obtain ⟨C, K₀, hC, hK, hBound⟩ := strip_bound L hLt c
    obtain ⟨Cd, Kd₀, hCd, hKd, hBoundd⟩ := strip_bound Ld hLdt (1 - a)
    let B₁ (p : P) := C * ∫ x, ‖F (p, x)‖ * δ (p, x) ^ c ∂μ
    let B₂ (p : P) := Cd * ∫ x, ‖Fd (p, x)‖ * δd (p, x) ^ (1 - a) ∂ν
    have Hb₁ (p : P) : 0 ≤ B₁ p := mul_nonneg hC (integral_nonneg fun x =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hpos (p, x)).le _))
    have Hb₂ (p : P) : 0 ≤ B₂ p := mul_nonneg hCd (integral_nonneg fun x =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hposd (p, x)).le _))
    have hi₁ : Integrable B₁ η := (hi c hcb.le).integral_prod_left.const_mul C
    have hi₂ : Integrable B₂ η := (hid (1 - a) hab.le).integral_prod_left.const_mul Cd
    refine ⟨a, c, max K₀ Kd₀, hau, hvc, fun p => B₁ p + B₂ p, hi₁.add hi₂, ?_⟩
    filter_upwards [hE] with p hp
    refine ⟨add_nonneg (Hb₁ p) (Hb₂ p), fun s hs => ?_⟩
    rcases hs with hs | hs
    · have hsr : (1 - s).re = 1 - a := by simp [hs]
      have hRe : b < (1 - s).re := hsr ▸ hab
      have he : ‖Ld (1 - s)‖ ≤ Cd * Real.exp (Kd₀ * |s.im|) := by simpa using hBoundd (1 - s) hsr
      rw [show J p s = Ld (1 - s) * (∫ x, Kd (1 - s) (p, x) ∂ν) from by
        simpa only [sub_sub_cancel] using (hp (1 - s) hRe).2.symm]
      have hB := bound_product (Ld (1 - s)) (fun x => Kd (1 - s) (p, x)) ν Cd
        (Real.exp (Kd₀ * |s.im|)) he hCd (Real.exp_nonneg _)
      simp only [Kd, norm_MellinKernel hposd, hsr] at hB
      exact hB.trans (mul_le_mul (le_add_of_nonneg_left (Hb₁ p))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)))
        (Real.exp_nonneg _) (add_nonneg (Hb₁ p) (Hb₂ p)))
    · have hRe : b < s.re := hs ▸ hcb
      rw [← (hp s hRe).1]
      have hB := bound_product (L s) (fun x => K s (p, x)) μ C (Real.exp (K₀ * |s.im|))
        (hBound s hs) hC (Real.exp_nonneg _)
      simp only [K, norm_MellinKernel hpos, hs] at hB
      exact hB.trans (mul_le_mul (le_add_of_nonneg_right (Hb₂ p))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
        (Real.exp_nonneg _) (add_nonneg (Hb₁ p) (Hb₂ p)))
  obtain ⟨hJi, hJd⟩ := Langlands.Analysis.entireStripIntegral η J hM hJ hLines
  refine ⟨hJi, hJd, fun s hs => ?_⟩
  rw [integral_prod _ (hI s hs), ← integral_const_mul]
  exact integral_congr_ae (hE.mono fun p hp => (hp s hs).1.symm)

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinMarginal
