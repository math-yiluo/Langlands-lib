import Langlands.Global.ImaginaryAxisAveraging
import Langlands.Global.ImaginaryAxisCoordinates
import Langlands.Analysis.SeveralComplex.ParametricIntegral

/-! # Divisibility at a point of the imaginary axis from the averaged wave-packet bound

Abstract form of the core of Lapid's proof of Proposition 6. A family `h(s, g)`, holomorphic in
`s` near `s₀ = i x₀`, continuous and left `Γ`-invariant, whose quotients `h / Q` by a product
`Q` of root forms satisfy a wave-packet bound on the real slice, is divisible by `Q` near `s₀`
for every `g`, given a division lemma for locally uniform limits of functions whose quotients
by `Q` are square integrable on the real slice. -/

noncomputable section

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

section Translation

theorem setIntegral_comp_add_left {n : ℕ} (x₀ : Fin n → ℝ) (A : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) :
    ∫ x in A, f (x₀ + x) = ∫ x in (fun x => x₀ + x) '' A, f x := by
  have hmp : MeasurePreserving (fun x => x₀ + x) (volume : Measure (Fin n → ℝ)) volume :=
    measurePreserving_add_left volume x₀
  have hme : MeasurableEmbedding (fun x : Fin n → ℝ => x₀ + x) :=
    (Homeomorph.addLeft x₀).measurableEmbedding
  exact (hmp.setIntegral_image_emb hme f A).symm

theorem imaginarySlice_add {n : ℕ} (x₀ x : Fin n → ℝ) :
    (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ)) = imaginarySlice (x₀ + x) := by
  ext j
  simp [imaginarySlice, mul_add]

theorem continuous_imaginarySlice {n : ℕ} : Continuous (imaginarySlice (n := n)) :=
  continuous_pi fun j => continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))

end Translation

section Division

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [T2Space H] (Γ : Subgroup H)

attribute [local instance] quotient_opensMeasurableSpace

/-- **Local divisibility.** Under a wave-packet bound for `k = h / Q` on the real slice and a
division lemma for locally uniform limits (hypothesis `hdiv`), the neighbourhood `W'` of
`s₀ = i x₀` given by the division lemma works for every `g₀`: `h(·, g₀) = Q · H'` on `W'` with
`H'` holomorphic. -/
theorem exists_local_division (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    {n : ℕ} (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (x₀ : Fin n → ℝ) (W : Set (Fin n → ℂ)) (hW : IsOpen W)
    (h : (Fin n → ℂ) → H → ℂ)
    (hh : ContinuousOn (fun q : (Fin n → ℂ) × H => h q.1 q.2) (W ×ˢ univ))
    (hhol : ∀ g, DifferentiableOn ℂ (fun s => h s g) W)
    (hinv : ∀ s ∈ W, ∀ c ∈ Γ, ∀ g, h s (c * g) = h s g)
    (Q : (Fin n → ℂ) → ℂ) (hQ : Continuous Q)
    (k : (Fin n → ℝ) → H → ℂ)
    (hk : ∀ x, imaginarySlice x ∈ W → Q (imaginarySlice x) ≠ 0 → ∀ g,
      k x g = h (imaginarySlice x) g / Q (imaginarySlice x))
    (C : ℝ)
    (hwave : ∀ (c' : (Fin n → ℝ) → ℂ) (A : Set (Fin n → ℝ)), IsCompact A →
      A ⊆ {x | imaginarySlice x ∈ W ∧ Q (imaginarySlice x) ≠ 0} →
      Measurable c' → (∃ B : ℝ, ∀ x, ‖c' x‖ ≤ B) → (∀ x ∉ A, c' x = 0) →
      MemLp (fun y : LeftCosetSpace Γ => ∫ x, c' x * k x y.out ∂(c • volume)) 2
          (LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν) ∧
        ∫ y, ‖∫ x, c' x * k x y.out ∂(c • volume)‖ ^ 2
            ∂(LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν) ≤
          C * ∫ x, ‖c' x‖ ^ 2 ∂(c • volume))
    (ρ : ℝ)
    (hρ : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) ρ,
      (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ)) ∈ W)
    (hdiv : ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ imaginarySlice x₀ ∈ W' ∧ W' ⊆ W ∧
      ∀ (L : Filter (Set H)) [L.NeBot] (Hk : Set H → (Fin n → ℂ) → ℂ)
        (Hlim : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Hlim W →
        (∀ᶠ V in L, DifferentiableOn ℂ (Hk V) W) → TendstoLocallyUniformlyOn Hk Hlim L W →
        (∀ᶠ V in L, ∃ C' : ℝ, ∀ A : Set (Fin n → ℝ), IsCompact A →
          A ⊆ Metric.ball 0 ρ →
          (∀ x ∈ A, Q (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ)) ≠ 0) →
          ∫ x in A, ‖Hk V (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ)) /
            Q (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ))‖ ^ 2 ≤ C') →
        ∃ H' : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H' W' ∧ ∀ s ∈ W', Hlim s = Q s * H' s) :
    ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ imaginarySlice x₀ ∈ W' ∧ W' ⊆ W ∧
      ∀ g₀ : H, ∃ H' : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ H' W' ∧
        ∀ s ∈ W', h s g₀ = Q s * H' s := by
  classical
  obtain ⟨W', hW'o, hs₀, hW'W, hW'⟩ := hdiv
  refine ⟨W', hW'o, hs₀, hW'W, fun g₀ => ?_⟩
  have := shrinkingNhds_neBot g₀
  set μ := LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν with hμ
  -- the region of the real slice where `k = h / Q`
  set T : Set (Fin n → ℝ) := {x | imaginarySlice x ∈ W ∧ Q (imaginarySlice x) ≠ 0} with hTdef
  have hTo : IsOpen T :=
    (hW.preimage continuous_imaginarySlice).inter
      (isOpen_ne_fun (hQ.comp continuous_imaginarySlice) continuous_const)
  have hkcont : ContinuousOn (fun q : (Fin n → ℝ) × H => k q.1 q.2) (T ×ˢ univ) := by
    have h1 : ContinuousOn (fun q : (Fin n → ℝ) × H =>
        h (imaginarySlice q.1) q.2 / Q (imaginarySlice q.1)) (T ×ˢ univ) := by
      refine ContinuousOn.div ?_ ?_ fun q hq => hq.1.2
      · exact hh.comp ((continuous_imaginarySlice.comp continuous_fst).prodMk
          continuous_snd).continuousOn fun q hq => ⟨hq.1.1, mem_univ _⟩
      · exact (hQ.comp (continuous_imaginarySlice.comp continuous_fst)).continuousOn
    refine h1.congr fun q hq => ?_
    exact hk q.1 hq.1.1 hq.1.2 q.2
  have hkinv : ∀ x ∈ T, ∀ c ∈ Γ, ∀ g, k x (c * g) = k x g := by
    intro x hx c hc g
    rw [hk x hx.1 hx.2, hk x hx.1 hx.2, hinv _ hx.1 c hc]
  set Hk : Set H → (Fin n → ℂ) → ℂ := fun V s =>
    (μ.real (LeftCosetSpace.mk Γ '' V))⁻¹ • ∫ y in LeftCosetSpace.mk Γ '' V, h s y.out ∂μ
    with hHkdef
  refine hW' (shrinkingNhds g₀) Hk (fun s => h s g₀) (hhol g₀) ?_
    (tendstoLocallyUniformlyOn_average Γ hΓ ν h W hW hh hinv g₀) ?_
  · -- holomorphy of the averages
    refine eventually_shrinkingNhds univ_mem fun V _ hVo hgV hVc => ?_
    set N := LeftCosetSpace.mk Γ '' V with hNdef
    have hNo : IsOpen N := (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap V hVo
    have hNm : MeasurableSet N := measurableSet_of_isOpen Γ hNo
    have hμN : μ N < ∞ :=
      (measure_mk_image_le Γ hΓ ν hVo).trans_lt
        ((measure_mono subset_closure).trans_lt hVc.measure_lt_top)
    have : IsFiniteMeasure (μ.restrict N) := isFiniteMeasure_restrict.mpr hμN.ne
    have hcont_y : ∀ s ∈ W, Continuous fun y : LeftCosetSpace Γ => h s y.out := by
      intro s hs
      have h1 := continuousOn_out_of_invariant Γ h W hW hh hinv
      rw [← continuousOn_univ]
      exact h1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y _ => ⟨hs, mem_univ _⟩)
    have heq : (fun s => ∫ y in N, h s y.out ∂μ) =
        fun s => ∫ y, N.indicator (fun y => h s y.out) y ∂(μ.restrict N) := by
      ext s
      rw [integral_indicator hNm, Measure.restrict_restrict hNm, inter_self]
    show DifferentiableOn ℂ (fun s => (μ.real N)⁻¹ • ∫ y in N, h s y.out ∂μ) W
    suffices hd : DifferentiableOn ℂ (fun s => ∫ y in N, h s y.out ∂μ) W from
      hd.const_smul ((μ.real N)⁻¹)
    rw [heq]
    refine Langlands.Analysis.SeveralComplex.differentiableOn_integral_of_bounded (μ.restrict N)
      (fun s y => N.indicator (fun y => h s y.out) y) hW ?_ ?_ ?_
    · intro y
      by_cases hy : y ∈ N
      · simp only [Set.indicator_of_mem hy]
        exact hhol y.out
      · simp only [Set.indicator_of_notMem hy]
        exact differentiableOn_const 0
    · intro s hs
      exact ((hcont_y s hs).aestronglyMeasurable).indicator hNm
    · intro K hKW hK
      obtain ⟨B, hB⟩ := (hK.prod hVc).exists_bound_of_continuousOn
        (hh.mono (prod_mono hKW (subset_univ _)))
      refine ⟨max B 0, fun s hs y => ?_⟩
      by_cases hy : y ∈ N
      · rw [Set.indicator_of_mem hy]
        obtain ⟨g, hg, rfl⟩ := hy
        rw [apply_out_of_invariant Γ (h s) (hinv s (hKW hs)) g]
        exact (hB (s, g) ⟨hs, subset_closure hg⟩).trans (le_max_left _ _)
      · rw [Set.indicator_of_notMem hy, norm_zero]
        exact le_max_right _ _
  · -- the square-integrability bound on the real slice
    refine eventually_shrinkingNhds univ_mem fun V _ hVo hgV hVc => ?_
    set N := LeftCosetSpace.mk Γ '' V with hNdef
    set K : (Fin n → ℝ) → ℂ := fun x => ∫ y in N, k x y.out ∂μ with hKdef
    have hbound : ∀ A' : Set (Fin n → ℝ), IsCompact A' → A' ⊆ T →
        ∫ x in A', ‖K x‖ ^ 2 ∂(c • volume) ≤ max C 0 * μ.real N := by
      intro A' hA' hA'T
      have : IsFiniteMeasureOnCompacts ((c • volume : Measure (Fin n → ℝ))) := by
        refine ⟨fun S hS => ?_⟩
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top hctop.lt_top hS.measure_lt_top
      exact setIntegral_norm_sq_average_le Γ hΓ ν (c • volume) k T hTo hkcont hkinv C
        hwave hVo hVc hA' hA'T
    refine ⟨(μ.real N)⁻¹ ^ 2 * (c.toReal⁻¹ * (max C 0 * μ.real N)),
      fun A hA hAρ hAQ => ?_⟩
    set A' := (fun x => x₀ + x) '' A with hA'def
    have hA' : IsCompact A' := hA.image (continuous_const.add continuous_id)
    have hA'T : A' ⊆ T := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 := hρ x (hAρ hx)
      have h2 := hAQ x hx
      rw [imaginarySlice_add] at h1 h2
      exact ⟨h1, h2⟩
    have hpt : ∀ x ∈ A,
        ‖Hk V (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ)) /
          Q (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ))‖ ^ 2 =
        (μ.real N)⁻¹ ^ 2 * ‖K (x₀ + x)‖ ^ 2 := by
      intro x hx
      have h1 := hρ x (hAρ hx)
      have h2 := hAQ x hx
      rw [imaginarySlice_add] at h1 h2 ⊢
      have hK : K (x₀ + x) = (∫ y in N, h (imaginarySlice (x₀ + x)) y.out ∂μ) /
          Q (imaginarySlice (x₀ + x)) := by
        simp only [K]
        rw [← integral_div]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact hk (x₀ + x) h1 h2 y.out
      simp only [Hk, hK, smul_div_assoc, norm_smul, mul_pow, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg measureReal_nonneg, inv_pow]
      rfl
    have hcalc : ∫ x in A, ‖Hk V (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ)) /
          Q (fun j => imaginarySlice x₀ j + Complex.I * (x j : ℂ))‖ ^ 2 =
        (μ.real N)⁻¹ ^ 2 * (c.toReal⁻¹ * ∫ x in A', ‖K x‖ ^ 2 ∂(c • volume)) := by
      rw [setIntegral_congr_fun hA.isClosed.measurableSet hpt, integral_const_mul,
        setIntegral_comp_add_left x₀ A (fun x => ‖K x‖ ^ 2), Measure.restrict_smul,
        integral_smul_measure, smul_eq_mul,
        inv_mul_cancel_left₀ (ENNReal.toReal_pos hc0 hctop).ne']
    rw [hcalc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (hbound A' hA' hA'T)
      (inv_nonneg.mpr ENNReal.toReal_nonneg)

end Division

end Langlands.Global.ImaginaryAxis
