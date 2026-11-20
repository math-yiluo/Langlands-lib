import Langlands.Global.LeftCosetFundamentalDomain
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Averages over small sets of `Γ \ H` and the wave-packet bound

Generic measure theory on the quotient of a second countable locally compact group by a
discrete subgroup, used in the proof of Lapid's Proposition 6. -/

noncomputable section

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

section Quotient

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (Γ : Subgroup H)

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem exists_mul_eq_out (g : H) :
    ∃ c ∈ Γ, (LeftCosetSpace.mk Γ g).out = c * g := by
  have h : LeftCosetSpace.mk Γ (LeftCosetSpace.mk Γ g).out = LeftCosetSpace.mk Γ g :=
    Quotient.out_eq _
  rw [LeftCosetSpace.mk_eq_mk_iff] at h
  refine ⟨(LeftCosetSpace.mk Γ g).out * g⁻¹, ?_, by simp⟩
  simpa [mul_inv_rev] using Γ.inv_mem h

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem apply_out_of_invariant {α : Type*} (f : H → α)
    (hf : ∀ c ∈ Γ, ∀ g, f (c * g) = f g) (g : H) :
    f (LeftCosetSpace.mk Γ g).out = f g := by
  obtain ⟨c, hc, h⟩ := exists_mul_eq_out Γ g
  rw [h, hf c hc]

theorem continuousOn_out_of_invariant {E α : Type*} [TopologicalSpace E] [TopologicalSpace α]
    (f : E → H → α) (W : Set E) (hW : IsOpen W)
    (hf : ContinuousOn (fun q : E × H => f q.1 q.2) (W ×ˢ univ))
    (hinv : ∀ s ∈ W, ∀ c ∈ Γ, ∀ g, f s (c * g) = f s g) :
    ContinuousOn (fun q : E × LeftCosetSpace Γ => f q.1 q.2.out) (W ×ˢ univ) := by
  have hq : IsQuotientMap
      (Prod.map id (LeftCosetSpace.mk Γ) : E × H → E × LeftCosetSpace Γ) :=
    (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).isQuotientMap
  rw [hq.continuousOn_isOpen_iff (hW.prod isOpen_univ)]
  have hpre : (Prod.map id (LeftCosetSpace.mk Γ)) ⁻¹'
      (W ×ˢ (univ : Set (LeftCosetSpace Γ))) = W ×ˢ (univ : Set H) := by
    ext q; simp
  rw [hpre]
  refine hf.congr ?_
  rintro ⟨s, g⟩ ⟨hs, -⟩
  exact apply_out_of_invariant Γ (f s) (hinv s hs) g

omit [IsTopologicalGroup H] in
theorem measurableSet_of_isOpen [MeasurableSpace H] [OpensMeasurableSpace H]
    {U : Set (LeftCosetSpace Γ)} (hU : IsOpen U) : MeasurableSet U :=
  measurableSet_quotient.mpr ((hU.preimage (LeftCosetSpace.continuous_mk Γ)).measurableSet)

variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem measure_mk_image_pos (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] [ν.IsOpenPosMeasure] {V : Set H} (hV : IsOpen V)
    (hne : V.Nonempty) :
    0 < LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν (LeftCosetSpace.mk Γ '' V) := by
  have := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  have hO : IsOpen (LeftCosetSpace.mk Γ '' V) :=
    (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap V hV
  rw [LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure_apply Γ ν _
    (measurableSet_of_isOpen Γ hO)]
  set t := LeftCosetSpace.mk Γ ⁻¹' (LeftCosetSpace.mk Γ '' V)
  have hfd := LeftCosetSpace.isFundamentalDomain Γ hΓ ν
  have hinv : ∀ c : Γ, c • t = t := by
    intro c
    ext x
    simp only [t, mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_image]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨y, hy, ?_⟩
      rw [hyx]
      have : (c⁻¹ • x : H) = ((c⁻¹ : Γ) : H) * x := rfl
      rw [this, LeftCosetSpace.mk_subgroup_mul]
    · rintro ⟨y, hy, hyx⟩
      refine ⟨y, hy, ?_⟩
      rw [hyx]
      have : (c⁻¹ • x : H) = ((c⁻¹ : Γ) : H) * x := rfl
      rw [this, LeftCosetSpace.mk_subgroup_mul]
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  have ht0 : ν t = 0 := hfd.measure_zero_of_invariant t hinv h0
  have hVt : V ⊆ t := fun x hx => ⟨x, hx, rfl⟩
  exact (hV.measure_ne_zero ν hne) (measure_mono_null hVt ht0)

theorem measure_mk_image_le (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] {V : Set H} (hV : IsOpen V) :
    LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν (LeftCosetSpace.mk Γ '' V) ≤ ν V := by
  have := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  have hO : IsOpen (LeftCosetSpace.mk Γ '' V) :=
    (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap V hV
  rw [LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure_apply Γ ν _
    (measurableSet_of_isOpen Γ hO)]
  have hfd := LeftCosetSpace.isFundamentalDomain Γ hΓ ν
  have hsub : LeftCosetSpace.mk Γ ⁻¹' (LeftCosetSpace.mk Γ '' V) ∩
      LeftCosetSpace.fundamentalDomain Γ hΓ ⊆
      ⋃ c : Γ, (c • V ∩ LeftCosetSpace.fundamentalDomain Γ hΓ) := by
    rintro x ⟨⟨y, hy, hyx⟩, hxs⟩
    rw [LeftCosetSpace.mk_eq_mk_iff] at hyx
    refine mem_iUnion.mpr ⟨⟨x * y⁻¹, hyx⟩, ?_, hxs⟩
    exact mem_smul_set.mpr ⟨y, hy, by simp [Subgroup.smul_def]⟩
  calc _ ≤ ν (⋃ c : Γ, (c • V ∩ LeftCosetSpace.fundamentalDomain Γ hΓ)) := measure_mono hsub
    _ ≤ ∑' c : Γ, ν (c • V ∩ LeftCosetSpace.fundamentalDomain Γ hΓ) := measure_iUnion_le _
    _ = ν V := (hfd.measure_eq_tsum V).symm

omit [IsTopologicalGroup H] [BorelSpace H] [SecondCountableTopology H] in
/-- Open sets of the quotient are measurable, so `Γ \ H` is an opens-measurable space. -/
theorem quotient_opensMeasurableSpace [OpensMeasurableSpace H] :
    OpensMeasurableSpace (LeftCosetSpace Γ) where
  borel_le := by
    refine MeasurableSpace.generateFrom_le fun U hU => ?_
    exact measurableSet_of_isOpen Γ hU

end Quotient

section Average

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (Γ : Subgroup H)

attribute [local instance] quotient_opensMeasurableSpace

/-- **Averaged wave-packet bound.** Let `k x g` be continuous on `T × H`, left `Γ`-invariant
in `g`, and suppose that every bounded measurable `c` vanishing outside a compact `A ⊆ T`
gives a wave packet `Θ_c(y) = ∫ c(x) k(x, y) dσ(x)` with `∫ |Θ_c|² ≤ C ∫ |c|²` on `Γ \ H`.
Then for the image `N` of an open relatively compact `V ⊆ H` and every compact `A ⊆ T`,
`∫_A |∫_N k(x, y) dy|² dσ(x) ≤ max C 0 · vol(N)`. -/
theorem setIntegral_norm_sq_average_le (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] [IsFiniteMeasureOnCompacts ν]
    {n : ℕ} (σ : Measure (Fin n → ℝ)) [SFinite σ] [IsFiniteMeasureOnCompacts σ]
    (k : (Fin n → ℝ) → H → ℂ) (T : Set (Fin n → ℝ)) (hT : IsOpen T)
    (hk : ContinuousOn (fun q : (Fin n → ℝ) × H => k q.1 q.2) (T ×ˢ univ))
    (hinv : ∀ x ∈ T, ∀ c ∈ Γ, ∀ g, k x (c * g) = k x g) (C : ℝ)
    (hwave : ∀ (c : (Fin n → ℝ) → ℂ) (A : Set (Fin n → ℝ)), IsCompact A → A ⊆ T →
      Measurable c → (∃ B : ℝ, ∀ x, ‖c x‖ ≤ B) → (∀ x ∉ A, c x = 0) →
      MemLp (fun y : LeftCosetSpace Γ => ∫ x, c x * k x y.out ∂σ) 2
          (LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν) ∧
        ∫ y, ‖∫ x, c x * k x y.out ∂σ‖ ^ 2 ∂(LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν) ≤
          C * ∫ x, ‖c x‖ ^ 2 ∂σ)
    {V : Set H} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {A : Set (Fin n → ℝ)} (hA : IsCompact A) (hAT : A ⊆ T) :
    ∫ x in A, ‖∫ y in LeftCosetSpace.mk Γ '' V, k x y.out
        ∂(LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν)‖ ^ 2 ∂σ ≤
      max C 0 * (LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν
        (LeftCosetSpace.mk Γ '' V)).toReal := by
  classical
  set μ := LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν with hμ
  set N := LeftCosetSpace.mk Γ '' V with hNdef
  have hNo : IsOpen N := (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap V hV
  have hNm : MeasurableSet N := measurableSet_of_isOpen Γ hNo
  have hμN : μ N < ∞ :=
    (measure_mk_image_le Γ hΓ ν hV).trans_lt
      ((measure_mono subset_closure).trans_lt hVc.measure_lt_top)
  have : IsFiniteMeasure (μ.restrict N) := isFiniteMeasure_restrict.mpr hμN.ne
  -- a bound for `k` on `A × closure V`
  have hAV : IsCompact (A ×ˢ closure V) := hA.prod hVc
  obtain ⟨B₀, hB₀⟩ := hAV.exists_bound_of_continuousOn
    (hk.mono (prod_mono hAT (subset_univ _)))
  set B := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hkB : ∀ x ∈ A, ∀ y ∈ N, ‖k x y.out‖ ≤ B := by
    rintro x hx y ⟨g, hg, rfl⟩
    rw [apply_out_of_invariant Γ (k x) (hinv x (hAT hx)) g]
    exact (hB₀ (x, g) ⟨hx, subset_closure hg⟩).trans (le_max_left _ _)
  -- continuity of `y ↦ k x y.out` for `x ∈ T`
  have hcont_y : ∀ x ∈ T, Continuous fun y : LeftCosetSpace Γ => k x y.out := by
    intro x hx
    have h := continuousOn_out_of_invariant Γ k T hT hk hinv
    rw [← continuousOn_univ]
    have : (fun y : LeftCosetSpace Γ => k x y.out) =
        (fun q : (Fin n → ℝ) × LeftCosetSpace Γ => k q.1 q.2.out) ∘ fun y => (x, y) := rfl
    rw [this]
    exact h.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨hx, mem_univ _⟩)
  -- the average `K`
  set K : (Fin n → ℝ) → ℂ := fun x => ∫ y in N, k x y.out ∂μ with hKdef
  have hKcont : ContinuousOn K A := by
    refine continuousOn_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · intro x hx
      exact (hcont_y x (hAT hx)).aestronglyMeasurable
    · intro x hx
      exact (ae_restrict_iff' hNm).mpr (Eventually.of_forall fun y hy => hkB x hx y hy)
    · refine Eventually.of_forall fun y => ?_
      have h1 : ContinuousOn (fun x => k x y.out) T :=
        hk.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun x hx => ⟨hx, mem_univ y.out⟩)
      exact h1.mono hAT
  have hKbound : ∀ x ∈ A, ‖K x‖ ≤ B * μ.real N := by
    intro x hx
    have := norm_setIntegral_le_of_norm_le_const hμN (fun y hy => hkB x hx y hy)
    simpa [mul_comm] using this
  -- the test coefficient `c = conj K` on `A`
  set c : (Fin n → ℝ) → ℂ := A.piecewise (fun x => (starRingEnd ℂ) (K x)) 0 with hcdef
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hcm : Measurable c :=
    ContinuousOn.measurable_piecewise (Complex.continuous_conj.comp_continuousOn hKcont)
      continuousOn_const hAm
  have hcB : ∀ x, ‖c x‖ ≤ B * μ.real N := by
    intro x
    by_cases hx : x ∈ A
    · simp only [c, Set.piecewise_eq_of_mem _ _ _ hx, Complex.norm_conj]
      exact hKbound x hx
    · simp only [c, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, norm_zero]
      exact mul_nonneg hB0 measureReal_nonneg
  have hc0 : ∀ x ∉ A, c x = 0 := fun x hx => by simp [c, hx]
  obtain ⟨hΘL2, hΘle⟩ := hwave c A hA hAT hcm ⟨_, hcB⟩ hc0
  set Θ : LeftCosetSpace Γ → ℂ := fun y => ∫ x, c x * k x y.out ∂σ with hΘdef
  -- Fubini on `N × ℝⁿ`
  have hUAm : MeasurableSet (univ ×ˢ A : Set (LeftCosetSpace Γ × (Fin n → ℝ))) :=
    MeasurableSet.univ.prod hAm
  set G : LeftCosetSpace Γ × (Fin n → ℝ) → ℂ :=
    fun q => (starRingEnd ℂ) (K q.2) * k q.2 q.1.out with hGdef
  have hfeq : (Function.uncurry fun (y : LeftCosetSpace Γ) (x : Fin n → ℝ) => c x * k x y.out) =
      (univ ×ˢ A).indicator G := by
    ext ⟨y, x⟩
    by_cases hx : x ∈ A
    · simp [c, G, hx, Set.indicator_of_mem, Set.mem_prod]
    · simp [c, G, hx]
  have hGcont : ContinuousOn G (univ ×ˢ A) := by
    have h1 : ContinuousOn (fun q : LeftCosetSpace Γ × (Fin n → ℝ) => (starRingEnd ℂ) (K q.2))
        (univ ×ˢ A) :=
      (Complex.continuous_conj.comp_continuousOn hKcont).comp continuous_snd.continuousOn
        (fun q hq => hq.2)
    have h2 : ContinuousOn (fun q : LeftCosetSpace Γ × (Fin n → ℝ) => k q.2 q.1.out)
        (univ ×ˢ A) :=
      (continuousOn_out_of_invariant Γ k T hT hk hinv).comp continuous_swap.continuousOn
        (fun q hq => ⟨hAT hq.2, mem_univ _⟩)
    exact h1.mul h2
  have hae : ∀ᵐ q ∂((μ.restrict N).prod σ), q.1 ∈ N := by
    rw [ae_iff]
    have : {q : LeftCosetSpace Γ × (Fin n → ℝ) | ¬ q.1 ∈ N} = Nᶜ ×ˢ univ := by
      ext q; simp
    rw [this, Measure.prod_prod, Measure.restrict_apply hNm.compl]
    simp
  have hint : Integrable
      (Function.uncurry fun (y : LeftCosetSpace Γ) (x : Fin n → ℝ) => c x * k x y.out)
      ((μ.restrict N).prod σ) := by
    rw [hfeq, integrable_indicator_iff hUAm]
    have hfin : ((μ.restrict N).prod σ) (univ ×ˢ A) < ∞ := by
      rw [Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact ENNReal.mul_lt_top hμN hA.measure_lt_top
    exact IntegrableOn.of_bound hfin (hGcont.aestronglyMeasurable hUAm) (B * μ.real N * B) (by
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hUAm] with q hq1 hq2
      simp only [G, norm_mul, Complex.norm_conj]
      exact mul_le_mul (hKbound q.2 hq2.2) (hkB q.2 hq2.2 q.1 hq1) (norm_nonneg _)
        (mul_nonneg hB0 measureReal_nonneg))
  have hswap : ∫ y in N, Θ y ∂μ = ∫ x, c x * K x ∂σ := by
    simp only [Θ, K]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact integral_const_mul (c x) _
  set I : ℝ := ∫ x in A, ‖K x‖ ^ 2 ∂σ with hIdef
  have hI0 : 0 ≤ I := setIntegral_nonneg hAm (fun x _ => sq_nonneg _)
  have hcK : ∀ x, c x * K x = A.indicator (fun x => ((‖K x‖ ^ 2 : ℝ) : ℂ)) x := by
    intro x
    by_cases hx : x ∈ A
    · simp only [c, Set.piecewise_eq_of_mem _ _ _ hx, Set.indicator_of_mem hx]
      rw [Complex.conj_mul']
      push_cast
      ring
    · simp [c, hx]
  have hcc : ∀ x, ‖c x‖ ^ 2 = A.indicator (fun x => ‖K x‖ ^ 2) x := by
    intro x
    by_cases hx : x ∈ A
    · simp [c, hx]
    · simp [c, hx]
  have hI1 : ∫ x, c x * K x ∂σ = (I : ℂ) := by
    simp_rw [hcK]
    rw [integral_indicator hAm, integral_complex_ofReal]
  have hI2 : ∫ x, ‖c x‖ ^ 2 ∂σ = I := by
    simp_rw [hcc]
    rw [integral_indicator hAm]
  -- Cauchy–Schwarz on `N`
  have hΘsq : Integrable (fun y => ‖Θ y‖ ^ 2) μ := by
    have := hΘL2.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa using this
  have hCS : (∫ y in N, ‖Θ y‖ ∂μ) ^ 2 ≤ μ.real N * ∫ y, ‖Θ y‖ ^ 2 ∂μ := by
    have hf : MemLp (fun _ : LeftCosetSpace Γ => (1 : ℝ)) (ENNReal.ofReal 2) (μ.restrict N) :=
      memLp_const 1
    have hg : MemLp (fun y => ‖Θ y‖) (ENNReal.ofReal 2) (μ.restrict N) := by
      simpa using hΘL2.norm.restrict N
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict N)
      Real.HolderConjugate.two_two (ae_of_all _ fun _ => zero_le_one)
      (ae_of_all _ fun y => norm_nonneg (Θ y)) hf hg
    simp only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at h
    have hrpow : ∀ y, ‖Θ y‖ ^ (2 : ℝ) = ‖Θ y‖ ^ 2 := fun y => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hrpow] at h
    have hb : ∫ y in N, ‖Θ y‖ ^ 2 ∂μ ≤ ∫ y, ‖Θ y‖ ^ 2 ∂μ :=
      setIntegral_le_integral hΘsq (ae_of_all _ fun _ => sq_nonneg _)
    have hb0 : 0 ≤ ∫ y in N, ‖Θ y‖ ^ 2 ∂μ := setIntegral_nonneg hNm fun _ _ => sq_nonneg _
    have ha0 : 0 ≤ (μ.restrict N).real univ := measureReal_nonneg
    have hl0 : 0 ≤ ∫ y in N, ‖Θ y‖ ∂μ := setIntegral_nonneg hNm fun _ _ => norm_nonneg _
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
    have h2 := pow_le_pow_left₀ hl0 h 2
    rw [mul_pow, Real.sq_sqrt ha0, Real.sq_sqrt hb0] at h2
    have hreal : (μ.restrict N).real univ = μ.real N := by
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ]
    rw [hreal] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hb measureReal_nonneg)
  set C' := max C 0 with hC'
  have hle1 : I ≤ ∫ y in N, ‖Θ y‖ ∂μ := by
    have h := norm_integral_le_integral_norm (μ := μ.restrict N) Θ
    rw [hswap, hI1, Complex.norm_real, Real.norm_of_nonneg hI0] at h
    exact h
  have hle2 : ∫ y, ‖Θ y‖ ^ 2 ∂μ ≤ C' * I := by
    rw [← hI2]
    exact hΘle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg fun _ => sq_nonneg _))
  have hsq : I ^ 2 ≤ μ.real N * (C' * I) := by
    calc I ^ 2 ≤ (∫ y in N, ‖Θ y‖ ∂μ) ^ 2 := pow_le_pow_left₀ hI0 hle1 2
      _ ≤ μ.real N * ∫ y, ‖Θ y‖ ^ 2 ∂μ := hCS
      _ ≤ μ.real N * (C' * I) := mul_le_mul_of_nonneg_left hle2 measureReal_nonneg
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hgoal : I ≤ C' * μ.real N := by
    rcases hI0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact mul_nonneg hC'0 measureReal_nonneg
    · have : I * I ≤ (C' * μ.real N) * I := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  exact hgoal

end Average

section Convergence

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (Γ : Subgroup H)

attribute [local instance] quotient_opensMeasurableSpace

/-- The filter of open, relatively compact neighbourhoods `V` of `g₀`, shrinking to `g₀`. -/
def shrinkingNhds (g₀ : H) : Filter (Set H) :=
  (𝓝 g₀).smallSets ⊓ 𝓟 {V | IsOpen V ∧ g₀ ∈ V ∧ IsCompact (closure V)}

omit [Group H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
theorem eventually_shrinkingNhds {g₀ : H} {P : Set H → Prop} {U : Set H} (hU : U ∈ 𝓝 g₀)
    (hP : ∀ V, V ⊆ U → IsOpen V → g₀ ∈ V → IsCompact (closure V) → P V) :
    ∀ᶠ V in shrinkingNhds g₀, P V := by
  have h1 : ∀ᶠ V in (𝓝 g₀).smallSets, V ⊆ U := eventually_smallSets_subset.mpr hU
  have h2 : ∀ᶠ V in 𝓟 {V : Set H | IsOpen V ∧ g₀ ∈ V ∧ IsCompact (closure V)},
      IsOpen V ∧ g₀ ∈ V ∧ IsCompact (closure V) := eventually_principal.mpr fun V hV => hV
  filter_upwards [inf_le_left (b := 𝓟 _) h1, inf_le_right (a := (𝓝 g₀).smallSets) h2]
    with V hV1 hV2
  exact hP V hV1 hV2.1 hV2.2.1 hV2.2.2

omit [Group H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
theorem shrinkingNhds_neBot [LocallyCompactSpace H] [T2Space H] (g₀ : H) : (shrinkingNhds g₀).NeBot := by
  rw [shrinkingNhds, inf_principal_neBot_iff]
  intro U hU
  obtain ⟨t, ht, htU⟩ := (hasBasis_smallSets (𝓝 g₀)).mem_iff.mp hU
  obtain ⟨K, hK, hKt, hKc⟩ := local_compact_nhds ht
  obtain ⟨V, hVK, hVo, hgV⟩ := mem_nhds_iff.mp hK
  refine ⟨V, htU (show V ⊆ t from hVK.trans hKt), hVo, hgV, ?_⟩
  exact hKc.of_isClosed_subset isClosed_closure (closure_minimal hVK hKc.isClosed)

/-- The averages `vol(N)⁻¹ ∫_N h(s, y) dy` over the images `N` of shrinking neighbourhoods
`V` of `g₀` converge to `h(s, g₀)` locally uniformly in `s ∈ W`. -/
theorem tendstoLocallyUniformlyOn_average (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
    [SMulInvariantMeasure Γ H ν] [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    {E : Type*} [TopologicalSpace E] [LocallyCompactSpace E]
    (h : E → H → ℂ) (W : Set E) (hW : IsOpen W)
    (hh : ContinuousOn (fun q : E × H => h q.1 q.2) (W ×ˢ univ))
    (hinv : ∀ s ∈ W, ∀ c ∈ Γ, ∀ g, h s (c * g) = h s g) (g₀ : H) :
    TendstoLocallyUniformlyOn
      (fun (V : Set H) (s : E) =>
        ((LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν).real (LeftCosetSpace.mk Γ '' V))⁻¹ •
          ∫ y in LeftCosetSpace.mk Γ '' V, h s y.out
            ∂(LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν))
      (fun s => h s g₀) (shrinkingNhds g₀) W := by
  set μ := LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν with hμ
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hW]
  intro K hKW hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hf : ContinuousOn (fun q : H × E => h q.2 q.1) (univ ×ˢ K) :=
    hh.comp continuous_swap.continuousOn (fun q hq => ⟨hKW hq.2, mem_univ _⟩)
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod (f := fun g s => h s g) hf (mem_univ g₀)
    (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hv
  refine eventually_shrinkingNhds hv fun V hVv hVo hgV hVc => ?_
  intro s hs
  set N := LeftCosetSpace.mk Γ '' V with hNdef
  have hNo : IsOpen N := (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap V hVo
  have hNm : MeasurableSet N := measurableSet_of_isOpen Γ hNo
  have hμN : μ N < ∞ :=
    (measure_mk_image_le Γ hΓ ν hVo).trans_lt
      ((measure_mono subset_closure).trans_lt hVc.measure_lt_top)
  have hμN0 : 0 < μ N := measure_mk_image_pos Γ hΓ ν hVo ⟨g₀, hgV⟩
  have hreal : 0 < μ.real N := ENNReal.toReal_pos hμN0.ne' hμN.ne
  have : IsFiniteMeasure (μ.restrict N) := isFiniteMeasure_restrict.mpr hμN.ne
  have hclose : ∀ y ∈ N, dist (h s y.out) (h s g₀) < ε / 2 := by
    rintro y ⟨g, hg, rfl⟩
    rw [apply_out_of_invariant Γ (h s) (hinv s (hKW hs)) g]
    exact hvK g (hVv hg) s hs
  have hcont : Continuous fun y : LeftCosetSpace Γ => h s y.out := by
    have h1 := continuousOn_out_of_invariant Γ h W hW hh hinv
    rw [← continuousOn_univ]
    exact h1.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨hKW hs, mem_univ _⟩)
  have hint : Integrable (fun y : LeftCosetSpace Γ => h s y.out) (μ.restrict N) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable (‖h s g₀‖ + ε / 2) ?_
    filter_upwards [ae_restrict_mem hNm] with y hy
    have := hclose y hy
    rw [dist_eq_norm] at this
    calc ‖h s y.out‖ = ‖(h s y.out - h s g₀) + h s g₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖h s y.out - h s g₀‖ + ‖h s g₀‖ := norm_add_le _ _
      _ ≤ ‖h s g₀‖ + ε / 2 := by linarith
  have hdiff : (μ.real N)⁻¹ • ∫ y in N, h s y.out ∂μ - h s g₀ =
      (μ.real N)⁻¹ • ∫ y in N, (h s y.out - h s g₀) ∂μ := by
    rw [integral_sub hint (integrable_const _), smul_sub, setIntegral_const, smul_smul,
      inv_mul_cancel₀ hreal.ne', one_smul]
  rw [dist_comm, dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hreal.le)]
  have hbound : ‖∫ y in N, (h s y.out - h s g₀) ∂μ‖ ≤ ε / 2 * μ.real N := by
    have := norm_setIntegral_le_of_norm_le_const hμN (C := ε / 2)
      (fun y hy => by have := hclose y hy; rw [dist_eq_norm] at this; exact this.le)
    simpa [Measure.real] using this
  calc (μ.real N)⁻¹ * ‖∫ y in N, (h s y.out - h s g₀) ∂μ‖
      ≤ (μ.real N)⁻¹ * (ε / 2 * μ.real N) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hreal.le)
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

end Convergence

end Langlands.Global.ImaginaryAxis
