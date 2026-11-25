import Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure
import Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral
import Mathlib.LinearAlgebra.QuadraticForm.Basis

/-!
# The Weil index

GKT §3.1: characters of second degree (3.1.3, (3.6), Remark 3.1), the Weil index (Theorem 3.3,
Definition 3.4), and the Weil index as a normalized integral over large compact open subgroups
(Corollary 3.6, Proposition 3.10, Corollaries 3.11 and 3.12); from §3.2, Proposition 3.13 (a), (d)
(invariance under isomorphisms, products).

A **character of second degree** on a totally disconnected group `X` is a locally constant
`f : X → ℂ¹` whose bicharacter `e(x, y) = f(x + y) f(x)⁻¹ f(y)⁻¹` (`secondDegreeBicharacter`) is
self-dual (`IsCharacterOfSecondDegree`); for a quadratic form `q` with non-degenerate polar form on
a finite-dimensional vector space over a nonarchimedean local field and a non-trivial character
`ψ`, `x ↦ ψ(q x)` is one (`isCharacterOfSecondDegree_quadraticForm`), with `e = ψ ∘ polar q`. In the
book's notation `q = ½ q_b`, `polar q = b` and `f = f_b`.

For a Haar measure `μ`, the integrals of `f` over compact open subgroups `L ⊇ M^⊥` (`M` a compact
open subgroup on which `f = 1`) do not depend on `L` (`setIntegral_eq_setIntegral_annihilator`,
the computation of Proposition 3.10), so `f` has a Gauss integral `γ_μ` (`exists_hasGaussIntegral`,
unique: `HasGaussIntegral.eq`), and `γ_μ conj(γ_μ) = C(μ)`, the constant of Fourier inversion
(`hasGaussIntegral_mul_conj`): for large `L`, `|∫_L f|² = μ(L) ∫_{L^⊥} f = μ(L) μ(L^⊥)`.

The **Weil index** `weilIndex f` is the Gauss integral for the self-dual measure; it has modulus
one (`norm_weilIndex`), the Gauss integral for any Haar measure is `C(μ)^{1/2} γ(f)`
(`hasGaussIntegral_weilIndex`; the book's `|β_b|^{-1/2} = C(μ)^{1/2}`), so
`γ(f) = ∫_L f / |∫_L f|` for large `L` (`weilIndex_eq_div_norm`, Corollary 3.12), and
`γ(f) = 1` if `f` is trivial on a compact open subgroup equal to its annihilator (Corollary 3.11).
Theorem 3.3: `C(μ)^{-1/2} ℱ(φ ∗ f) = γ(f) ℱφ · f⁻¹` (`bicharacterFourier_convolution`), from Weil's
formula; Corollary 3.6 is its value at `0`.
-/

noncomputable section

open MeasureTheory
open scoped Topology NNReal ENNReal

namespace Langlands.Theta

open Langlands.HarmonicAnalysis

section Defs

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X]

/-- The bicharacter `(x, y) ↦ f(x + y) f(x)⁻¹ f(y)⁻¹` of a function `f` (GKT (3.6)). -/
def secondDegreeBicharacter (f : X → ℂ) : X → X → ℂ :=
  fun x y => f (x + y) * (f x)⁻¹ * (f y)⁻¹

/-- A **character of second degree** (GKT 3.1.3, Remark 3.1, after A. Weil): a locally constant
function `f : X → ℂ` of modulus one whose bicharacter `f(x + y) f(x)⁻¹ f(y)⁻¹` is self-dual
(Weil's "non-degenerate"). -/
structure IsCharacterOfSecondDegree (f : X → ℂ) : Prop where
  norm_eq_one : ∀ x, ‖f x‖ = 1
  isLocallyConstant : IsLocallyConstant f
  isSelfDualBicharacter : IsSelfDualBicharacter (secondDegreeBicharacter f)

/-- **The Weil index** `γ(f)` of a character of second degree (GKT Definition 3.4): its Gauss
integral for the self-dual measure of its bicharacter, the constant of Theorem 3.3
(`bicharacterFourier_convolution`), of modulus one (`norm_weilIndex`). For `f = ψ ∘ q`, `q` a
quadratic form, this is the book's `γ(ψ ∘ q)`. (`1` if the Gauss integral does not exist.) -/
def weilIndex (f : X → ℂ) : ℂ :=
  letI : MeasurableSpace X := borel X
  open Classical in
  if h : ∃ γ : ℂ, HasGaussIntegral (selfDualMeasure (secondDegreeBicharacter f)) f γ then
    h.choose
  else 1

end Defs

/-- Gauss integrals for `rμ` are `r` times those for `μ`. -/
theorem HasGaussIntegral.smul_measure {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {γ : ℂ} (h : HasGaussIntegral μ f γ)
    (r : ℝ≥0) : HasGaussIntegral (r • μ) f ((r : ℝ) * γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hL⟩ := h K hK
  refine ⟨L, hLc, hLo, hKL, ?_⟩
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, hL, NNReal.smul_def, Complex.real_smul]

namespace IsCharacterOfSecondDegree

section Algebra

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] {f : X → ℂ}

theorem ne_zero (hf : IsCharacterOfSecondDegree f) (x : X) : f x ≠ 0 := by
  intro h
  have := hf.norm_eq_one x
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- `f(x + y) = f(x) f(y) e(x, y)` (GKT (3.6)). -/
theorem map_add (hf : IsCharacterOfSecondDegree f) (x y : X) :
    f (x + y) = f x * f y * secondDegreeBicharacter f x y := by
  simp only [secondDegreeBicharacter]
  field_simp [hf.ne_zero x, hf.ne_zero y]

theorem map_zero (hf : IsCharacterOfSecondDegree f) : f 0 = 1 := by
  have h := hf.isSelfDualBicharacter.map_zero_left 0
  simp only [secondDegreeBicharacter, add_zero] at h
  rw [mul_inv_cancel₀ (hf.ne_zero 0), one_mul] at h
  exact inv_eq_one.mp h

theorem continuous (hf : IsCharacterOfSecondDegree f) : Continuous f :=
  hf.isLocallyConstant.continuous

theorem mul_conj (hf : IsCharacterOfSecondDegree f) (x : X) : f x * starRingEnd ℂ (f x) = 1 := by
  rw [Complex.mul_conj', hf.norm_eq_one]; simp

omit [TopologicalSpace X] in
/-- The bicharacter of a function with `f(x + y) = f(x) f(y) e(x, y)` is `e`. -/
theorem _root_.Langlands.Theta.secondDegreeBicharacter_eq {e : X → X → ℂ} (hne : ∀ x, f x ≠ 0)
    (hfe : ∀ x y, f (x + y) = f x * f y * e x y) : secondDegreeBicharacter f = e := by
  funext x y
  simp only [secondDegreeBicharacter, hfe]
  field_simp [hne x, hne y]

/-- A locally constant function of modulus one with `f(x + y) = f(x) f(y) e(x, y)` for a
self-dual bicharacter `e` is a character of second degree. -/
theorem of_bicharacter {e : X → X → ℂ} (he : IsSelfDualBicharacter e) (hn : ∀ x, ‖f x‖ = 1)
    (hlc : IsLocallyConstant f) (hfe : ∀ x y, f (x + y) = f x * f y * e x y) :
    IsCharacterOfSecondDegree f := by
  have hne : ∀ x, f x ≠ 0 := fun x h => by
    have := hn x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  exact ⟨hn, hlc, (secondDegreeBicharacter_eq hne hfe) ▸ he⟩

/-- A subgroup on which `f = 1` is contained in its annihilator. -/
theorem subset_annihilator (hf : IsCharacterOfSecondDegree f) {M : AddSubgroup X}
    (hM : ∀ x ∈ M, f x = 1) :
    (M : Set X) ⊆ hf.isSelfDualBicharacter.annihilator (M : Set X) := by
  intro x hx y hy
  simp only [secondDegreeBicharacter, hM _ (M.add_mem hy hx), hM y hy, hM x hx, inv_one,
    mul_one]

end Algebra

section Analysis

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] {f : X → ℂ}

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem isCompact_annihilator (hf : IsCharacterOfSecondDegree f) {M : AddSubgroup X}
    (hMc : IsCompact (M : Set X)) (hMo : IsOpen (M : Set X)) :
    IsCompact (hf.isSelfDualBicharacter.annihilator (M : Set X) : Set X) := by
  obtain ⟨K, hK, hKM⟩ := hf.isSelfDualBicharacter.big (M : Set X) (hMo.mem_nhds M.zero_mem)
  exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _
    (hf.isSelfDualBicharacter.isOpen_annihilator hMc)) fun y hy => hKM y hy

/-- **The integral of a character of second degree over a large compact open subgroup** (the
computation of GKT Proposition 3.10): if `f = 1` on the compact open subgroup `M`, then for every
compact open subgroup `L ⊇ M^⊥`, `∫_L f = ∫_{M^⊥} f`. -/
theorem setIntegral_eq_setIntegral_annihilator (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] {M : AddSubgroup X} (hMc : IsCompact (M : Set X))
    (hMo : IsOpen (M : Set X)) (hM : ∀ x ∈ M, f x = 1) {L : AddSubgroup X}
    (hLc : IsCompact (L : Set X)) (hLo : IsOpen (L : Set X))
    (hML : (hf.isSelfDualBicharacter.annihilator (M : Set X) : Set X) ⊆ L) :
    ∫ x in (L : Set X), f x ∂μ =
      ∫ x in (hf.isSelfDualBicharacter.annihilator (M : Set X) : Set X), f x ∂μ := by
  set e := secondDegreeBicharacter f
  have he : IsSelfDualBicharacter e := hf.isSelfDualBicharacter
  have hMsub : (M : Set X) ⊆ L := (hf.subset_annihilator hM).trans hML
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hMm : MeasurableSet (M : Set X) := hMo.measurableSet
  have hAo : IsOpen (he.annihilator (M : Set X) : Set X) := he.isOpen_annihilator hMc
  have hAm : MeasurableSet (he.annihilator (M : Set X) : Set X) := hAo.measurableSet
  have : IsFiniteMeasure (μ.restrict (L : Set X)) :=
    isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  have : IsFiniteMeasure (μ.restrict (M : Set X)) :=
    isFiniteMeasure_restrict.mpr hMc.measure_lt_top.ne
  -- for `m ∈ M`, `∫_L f(x) e(x, m) dx = ∫_L f(x + m) dx = A`
  have h1 : ∀ m ∈ (M : Set X), ∫ x in (L : Set X), f x * e x m ∂μ = ∫ x in (L : Set X), f x ∂μ := by
    intro m hm
    rw [← GaussIntegral.Internal.setIntegral_addSubgroup_add_right μ L hLo f (hMsub hm)]
    congr 1
    funext x
    rw [hf.map_add x m, hM m hm, mul_one]
  have hint : Integrable (Function.uncurry fun m x => f x * e x m)
      ((μ.restrict (M : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.continuous.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · simp [Function.uncurry, hf.norm_eq_one, he.norm_eq_one]
  have h3 := integral_integral_swap hint
  rw [setIntegral_congr_fun hMm h1, setIntegral_const] at h3
  -- `∫_M e(x, m) dm = μ(M) 1_{M^⊥}(x)`
  have h4 : ∀ x, ∫ m in (M : Set X), f x * e x m ∂μ =
      f x * (he.annihilator (M : Set X) : Set X).indicator
        (fun _ => (μ.real (M : Set X) : ℂ)) x := by
    intro x
    rw [integral_const_mul, ← BicharacterFourier.Internal.bicharacterFourier_indicator μ he M hMo x,
      bicharacterFourier, ← integral_indicator hMm]
    congr 2
    funext m
    by_cases hm : m ∈ (M : Set X) <;> simp [hm]
  simp_rw [h4] at h3
  have h5 : (fun x => f x * (he.annihilator (M : Set X) : Set X).indicator
      (fun _ => (μ.real (M : Set X) : ℂ)) x) =
      (he.annihilator (M : Set X) : Set X).indicator (fun x => (μ.real (M : Set X) : ℂ) * f x) := by
    funext x
    by_cases hx : x ∈ (he.annihilator (M : Set X) : Set X) <;> simp [hx, mul_comm]
  rw [h5, integral_indicator hAm, Measure.restrict_restrict hAm, Set.inter_eq_left.mpr hML,
    integral_const_mul, Complex.real_smul] at h3
  have hpos : ((μ.real (M : Set X) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne',
      hMc.measure_lt_top.ne⟩
  exact mul_left_cancel₀ hpos h3

variable [CompactOpenExhaustion X]

omit [IsTopologicalAddGroup X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- A compact open subgroup on which `f = 1`. -/
theorem exists_addSubgroup_eq_one (hf : IsCharacterOfSecondDegree f) :
    ∃ M : AddSubgroup X, IsCompact (M : Set X) ∧ IsOpen (M : Set X) ∧ ∀ x ∈ M, f x = 1 := by
  have hU : {x | f x = 1} ∈ 𝓝 (0 : X) :=
    (hf.isLocallyConstant.isOpen_fiber 1).mem_nhds (by simp [hf.map_zero])
  obtain ⟨M, hMc, hMo, hMU⟩ := CompactOpenExhaustion.exists_subset _ hU
  exact ⟨M, hMc, hMo, fun x hx => hMU hx⟩

/-- **The integrals of a character of second degree over large compact open subgroups are
constant** (GKT Proposition 3.10, Corollary 3.12: "the limit eventually stabilizes"). -/
theorem exists_setIntegral_eq (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] :
    ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) →
      IsOpen (L : Set X) → K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  obtain ⟨M, hMc, hMo, hM⟩ := hf.exists_addSubgroup_eq_one
  exact ⟨_, _, hf.isCompact_annihilator hMc hMo, fun L hLc hLo hKL =>
    hf.setIntegral_eq_setIntegral_annihilator μ hMc hMo hM hLc hLo hKL⟩

/-- A character of second degree has a Gauss integral for every Haar measure. -/
theorem exists_hasGaussIntegral (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] : ∃ γ, HasGaussIntegral μ f γ := by
  obtain ⟨γ, K₀, hK₀, hγ⟩ := hf.exists_setIntegral_eq μ
  refine ⟨γ, fun K hK => ?_⟩
  obtain ⟨L, hLc, hLo, hL⟩ := CompactOpenExhaustion.exists_superset (K ∪ K₀) (hK.union hK₀)
  exact ⟨L, hLc, hLo, Set.subset_union_left.trans hL,
    hγ L hLc hLo (Set.subset_union_right.trans hL)⟩

/-- The Gauss integral of a character of second degree is unique. -/
theorem hasGaussIntegral_unique (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] {γ γ' : ℂ} (h : HasGaussIntegral μ f γ) (h' : HasGaussIntegral μ f γ') :
    γ = γ' := by
  obtain ⟨γ₀, K, hK, hγ₀⟩ := hf.exists_setIntegral_eq μ
  obtain ⟨L, hLc, hLo, hKL, hL⟩ := h K hK
  obtain ⟨L', hLc', hLo', hKL', hL'⟩ := h' K hK
  rw [← hL, ← hL', hγ₀ L hLc hLo hKL, hγ₀ L' hLc' hLo' hKL']

variable [LocallyCompactSpace X]

/-- The constant of Fourier inversion is `μ(L) μ(L^⊥)` for every compact open subgroup `L`. -/
theorem bicharacterFourierConstant_eq_measureReal_mul (hf : IsCharacterOfSecondDegree f)
    (μ : Measure X) [μ.IsAddHaarMeasure] {L : AddSubgroup X} (hLc : IsCompact (L : Set X))
    (hLo : IsOpen (L : Set X)) :
    bicharacterFourierConstant μ (secondDegreeBicharacter f) = μ.real (L : Set X) *
      μ.real (hf.isSelfDualBicharacter.annihilator (L : Set X) : Set X) := by
  set e := secondDegreeBicharacter f
  have he : IsSelfDualBicharacter e := hf.isSelfDualBicharacter
  have hAo : IsOpen (he.annihilator (L : Set X) : Set X) := he.isOpen_annihilator hLc
  have h1 := bicharacterFourier_bicharacterFourier_eq he μ
    (HarmonicAnalysis.indicator_one_mem_schwartzBruhatSubmodule L hLc hLo) 0
  have h2 : bicharacterFourier μ e ((L : Set X).indicator fun _ => (1 : ℂ)) =
      fun y => (μ.real (L : Set X) : ℂ) *
        (he.annihilator (L : Set X) : Set X).indicator (fun _ => (1 : ℂ)) y := by
    funext y
    rw [BicharacterFourier.Internal.bicharacterFourier_indicator μ he L hLo y]
    by_cases hy : y ∈ (he.annihilator (L : Set X) : Set X)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [h2, bicharacterFourier_const_mul,
    BicharacterFourier.Internal.bicharacterFourier_indicator μ he _ hAo 0,
    Set.indicator_of_mem (he.annihilator _).zero_mem, neg_zero,
    Set.indicator_of_mem L.zero_mem, mul_one] at h1
  exact_mod_cast h1.symm

/-- **The Gauss integral has modulus `C(μ)^{1/2}`**: `γ_μ conj(γ_μ) = C(μ)`, the constant of
Fourier inversion (so the Gauss integral is `|β_b|^{-1/2}` times a number of modulus one, GKT
Lemma 3.9, Proposition 3.10). For a large compact open subgroup `L` with `L^⊥ ⊆ L`, `f = 1` on
`L^⊥`: `|∫_L f|² = ∫_{y ∈ L} ∫_{u ∈ L} f(u) e(y, u) = μ(L) ∫_{L^⊥} f = μ(L) μ(L^⊥)`. -/
theorem hasGaussIntegral_mul_conj (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] {γ : ℂ} (h : HasGaussIntegral μ f γ) :
    γ * starRingEnd ℂ γ = (bicharacterFourierConstant μ (secondDegreeBicharacter f) : ℂ) := by
  set e := secondDegreeBicharacter f
  have he : IsSelfDualBicharacter e := hf.isSelfDualBicharacter
  -- a compact open subgroup `M = N^⊥` with `f = 1` on `M` and `M^⊥⊥ ⊆ M`
  have hU : {x | f x = 1} ∈ 𝓝 (0 : X) :=
    (hf.isLocallyConstant.isOpen_fiber 1).mem_nhds (by simp [hf.map_zero])
  obtain ⟨K, hK, hKU⟩ := he.small _ hU
  obtain ⟨N, hNc, hNo, hKN⟩ := CompactOpenExhaustion.exists_superset K hK
  set M := he.annihilator (N : Set X) with hMdef
  have hMo : IsOpen (M : Set X) := he.isOpen_annihilator hNc
  have hMc : IsCompact (M : Set X) := hf.isCompact_annihilator hNc hNo
  have hM1 : ∀ x ∈ M, f x = 1 := fun x hx => hKU x fun y hy => hx y (hKN hy)
  have hNM : (N : Set X) ⊆ he.annihilator (M : Set X) := fun x hx y hy => by
    rw [he.symm]; exact hy x hx
  have hMM : (he.annihilator (he.annihilator (M : Set X) : Set X) : Set X) ⊆ M :=
    fun z hz x hx => hz x (hNM hx)
  obtain ⟨L, hLc, hLo, hML, hLγ⟩ := h _ (hf.isCompact_annihilator hMc hMo)
  have hLM : (he.annihilator (L : Set X) : Set X) ⊆ M := fun z hz => hMM fun w hw => hz w (hML hw)
  have hLL : (he.annihilator (L : Set X) : Set X) ⊆ L :=
    hLM.trans ((hf.subset_annihilator hM1).trans hML)
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hAo : IsOpen (he.annihilator (L : Set X) : Set X) := he.isOpen_annihilator hLc
  have hAm : MeasurableSet (he.annihilator (L : Set X) : Set X) := hAo.measurableSet
  have : IsFiniteMeasure (μ.restrict (L : Set X)) :=
    isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  -- `γ conj γ = ∫_{y ∈ L} ∫_{u ∈ L} f(u) e(u, y)`
  have h1 : γ * starRingEnd ℂ γ =
      ∫ y in (L : Set X), ∫ u in (L : Set X), f u * e u y ∂μ ∂μ := by
    rw [← hLγ, ← integral_conj, ← integral_const_mul]
    refine setIntegral_congr_fun hLm fun y hy => ?_
    rw [← GaussIntegral.Internal.setIntegral_addSubgroup_add_right μ L hLo f hy,
      ← integral_mul_const]
    congr 1
    funext u
    rw [hf.map_add u y]
    have := hf.mul_conj y
    linear_combination (f u * e u y) * this
  have hint : Integrable (Function.uncurry fun y u => f u * e u y)
      ((μ.restrict (L : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.continuous.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · simp [Function.uncurry, hf.norm_eq_one, he.norm_eq_one]
  rw [h1, integral_integral_swap hint]
  -- `∫_{y ∈ L} e(u, y) = μ(L) 1_{L^⊥}(u)`
  have h4 : ∀ u, ∫ y in (L : Set X), f u * e u y ∂μ =
      f u * (he.annihilator (L : Set X) : Set X).indicator
        (fun _ => (μ.real (L : Set X) : ℂ)) u := by
    intro u
    rw [integral_const_mul, ← BicharacterFourier.Internal.bicharacterFourier_indicator μ he L hLo u,
      bicharacterFourier, ← integral_indicator hLm]
    congr 2
    funext y
    by_cases hy : y ∈ (L : Set X) <;> simp [hy]
  simp_rw [h4]
  have h5 : (fun u => f u * (he.annihilator (L : Set X) : Set X).indicator
      (fun _ => (μ.real (L : Set X) : ℂ)) u) =
      (he.annihilator (L : Set X) : Set X).indicator (fun _ => (μ.real (L : Set X) : ℂ)) := by
    funext u
    by_cases hu : u ∈ (he.annihilator (L : Set X) : Set X)
    · rw [Set.indicator_of_mem hu, hM1 u (hLM hu), one_mul]
    · rw [Set.indicator_of_notMem hu, mul_zero]
  rw [h5, integral_indicator hAm, Measure.restrict_restrict hAm, Set.inter_eq_left.mpr hLL,
    setIntegral_const, Complex.real_smul,
    hf.bicharacterFourierConstant_eq_measureReal_mul μ hLc hLo]
  push_cast
  ring

/-- The Gauss integral of a character of second degree is not zero. -/
theorem hasGaussIntegral_ne_zero (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] {γ : ℂ} (h : HasGaussIntegral μ f γ) : γ ≠ 0 := by
  intro h0
  have := hf.hasGaussIntegral_mul_conj μ h
  rw [h0, zero_mul] at this
  exact (bicharacterFourierConstant_pos μ (secondDegreeBicharacter f)).ne'
    (by exact_mod_cast this.symm)

/-- `‖γ_μ‖ = C(μ)^{1/2}`. -/
theorem norm_hasGaussIntegral (hf : IsCharacterOfSecondDegree f) (μ : Measure X)
    [μ.IsAddHaarMeasure] {γ : ℂ} (h : HasGaussIntegral μ f γ) :
    ‖γ‖ = Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) := by
  have h1 := hf.hasGaussIntegral_mul_conj μ h
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_inj] at h1
  rw [← h1, Real.sqrt_sq (norm_nonneg _)]

end Analysis

end IsCharacterOfSecondDegree

/-! ### The Weil index -/

private theorem ofReal_mul_div_norm {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : ‖w‖ = 1) :
    (r : ℂ) * w / (‖(r : ℂ) * w‖ : ℂ) = w := by
  rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

section WeilIndex

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X] {f : X → ℂ}

/-- **The Gauss integral is `C(μ)^{1/2} γ(f)`** for every Haar measure `μ` (GKT Proposition 3.10,
Corollary 3.12, with the positive factor `|β_b|^{-1/2} = C(μ)^{1/2}` made explicit). -/
theorem hasGaussIntegral_weilIndex [MeasurableSpace X] [BorelSpace X]
    (hf : IsCharacterOfSecondDegree f) (μ : Measure X) [μ.IsAddHaarMeasure] :
    HasGaussIntegral μ f
      (Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) * weilIndex f) := by
  classical
  have hm : ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq
  subst hm
  let _ : MeasurableSpace X := borel X
  set e := secondDegreeBicharacter f
  have he : IsSelfDualBicharacter e := hf.isSelfDualBicharacter
  have : (selfDualMeasure e).IsAddHaarMeasure := isAddHaarMeasure_selfDualMeasure he
  have hex : ∃ γ : ℂ, HasGaussIntegral (selfDualMeasure e) f γ :=
    hf.exists_hasGaussIntegral (selfDualMeasure e)
  have hw : weilIndex f = hex.choose := by
    rw [weilIndex]
    exact dite_eq_left_of_eq_true (eq_true hex)
  have hC := bicharacterFourierConstant_pos μ e
  obtain ⟨γ, hγw, hγ⟩ : ∃ γ, weilIndex f = γ ∧ HasGaussIntegral (selfDualMeasure e) f γ :=
    ⟨hex.choose, hw, hex.choose_spec⟩
  have h1 := HasGaussIntegral.smul_measure hγ (Real.sqrt (bicharacterFourierConstant μ e)).toNNReal
  rw [selfDualMeasure_eq_smul he μ, smul_smul, Real.coe_toNNReal _ (Real.sqrt_nonneg _),
    ← Real.toNNReal_mul (Real.sqrt_nonneg _), mul_inv_cancel₀ (by positivity),
    Real.toNNReal_one, one_smul] at h1
  rwa [hγw]

/-- **The Weil index is the Gauss integral for the self-dual measure** (GKT Definition 3.4 with
Proposition 3.10). -/
theorem hasGaussIntegral_selfDualMeasure_weilIndex [MeasurableSpace X] [BorelSpace X]
    (hf : IsCharacterOfSecondDegree f) :
    HasGaussIntegral (selfDualMeasure (secondDegreeBicharacter f)) f (weilIndex f) := by
  have he := hf.isSelfDualBicharacter
  have : (selfDualMeasure (secondDegreeBicharacter f)).IsAddHaarMeasure :=
    isAddHaarMeasure_selfDualMeasure he
  have h := hasGaussIntegral_weilIndex hf (selfDualMeasure (secondDegreeBicharacter f))
  rwa [bicharacterFourierConstant_selfDualMeasure he, Real.sqrt_one, Complex.ofReal_one,
    one_mul] at h

/-- **The Weil index has modulus one** (GKT Theorem 3.3: `γ(f_b) ∈ ℂ¹`). -/
theorem norm_weilIndex (hf : IsCharacterOfSecondDegree f) : ‖weilIndex f‖ = 1 := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have he := hf.isSelfDualBicharacter
  have : (selfDualMeasure (secondDegreeBicharacter f)).IsAddHaarMeasure :=
    isAddHaarMeasure_selfDualMeasure he
  rw [hf.norm_hasGaussIntegral _ (hasGaussIntegral_selfDualMeasure_weilIndex hf),
    bicharacterFourierConstant_selfDualMeasure he, Real.sqrt_one]

theorem weilIndex_ne_zero (hf : IsCharacterOfSecondDegree f) : weilIndex f ≠ 0 := by
  intro h
  have := norm_weilIndex hf
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The Weil index is the phase of the Gauss integral** for any Haar measure (GKT
Corollary 3.12: `γ(f_b) = ∫_M f_b / |∫_M f_b|` for a large compact open subgroup `M`). -/
theorem weilIndex_eq_div_norm [MeasurableSpace X] [BorelSpace X]
    (hf : IsCharacterOfSecondDegree f) (μ : Measure X) [μ.IsAddHaarMeasure] {γ : ℂ}
    (h : HasGaussIntegral μ f γ) : weilIndex f = γ / ‖γ‖ := by
  rw [hf.hasGaussIntegral_unique μ h (hasGaussIntegral_weilIndex hf μ)]
  have hC := bicharacterFourierConstant_pos μ (secondDegreeBicharacter f)
  exact (ofReal_mul_div_norm (Real.sqrt_pos.2 hC) (norm_weilIndex hf)).symm

/-- **GKT Proposition 3.10** in the Library's form: if `f = 1` on a compact open subgroup `M`, then
for every compact open subgroup `L ⊇ M^⊥`, `∫_L f dμ = C(μ)^{1/2} γ(f)`; in particular
`γ(f) = ∫_L f / |∫_L f|`. -/
theorem setIntegral_eq_weilIndex [MeasurableSpace X] [BorelSpace X]
    (hf : IsCharacterOfSecondDegree f) (μ : Measure X) [μ.IsAddHaarMeasure] {M : AddSubgroup X}
    (hMc : IsCompact (M : Set X)) (hMo : IsOpen (M : Set X)) (hM : ∀ x ∈ M, f x = 1)
    {L : AddSubgroup X} (hLc : IsCompact (L : Set X)) (hLo : IsOpen (L : Set X))
    (hML : (hf.isSelfDualBicharacter.annihilator (M : Set X) : Set X) ⊆ L) :
    ∫ x in (L : Set X), f x ∂μ =
      Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) * weilIndex f := by
  have hγ : HasGaussIntegral μ f
      (∫ x in (hf.isSelfDualBicharacter.annihilator (M : Set X) : Set X), f x ∂μ) := by
    intro K hK
    obtain ⟨L', hLc', hLo', hL'⟩ := CompactOpenExhaustion.exists_superset
      (K ∪ (hf.isSelfDualBicharacter.annihilator (M : Set X) : Set X))
      (hK.union (hf.isCompact_annihilator hMc hMo))
    exact ⟨L', hLc', hLo', Set.subset_union_left.trans hL',
      hf.setIntegral_eq_setIntegral_annihilator μ hMc hMo hM hLc' hLo'
        (Set.subset_union_right.trans hL')⟩
  rw [hf.setIntegral_eq_setIntegral_annihilator μ hMc hMo hM hLc hLo hML]
  exact hf.hasGaussIntegral_unique μ hγ (hasGaussIntegral_weilIndex hf μ)

/-- **GKT Corollary 3.11**: if `f = 1` on a compact open subgroup `L` equal to its annihilator
(a self-dual lattice), then `γ(f) = 1`. -/
theorem weilIndex_eq_one (hf : IsCharacterOfSecondDegree f) {L : AddSubgroup X}
    (hLc : IsCompact (L : Set X)) (hLo : IsOpen (L : Set X)) (hL : ∀ x ∈ L, f x = 1)
    (hLL : hf.isSelfDualBicharacter.annihilator (L : Set X) = L) : weilIndex f = 1 := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := Measure.addHaar
  have h := setIntegral_eq_weilIndex hf μ hLc hLo hL hLc hLo (by rw [hLL])
  rw [setIntegral_congr_fun hLo.measurableSet (g := fun _ => (1 : ℂ)) hL, setIntegral_const] at h
  have hC := bicharacterFourierConstant_pos μ (secondDegreeBicharacter f)
  have hpos : 0 < μ.real (L : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLc.measure_lt_top.ne
  have h2 : weilIndex f = ((μ.real (L : Set X) /
      Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) : ℝ) : ℂ) := by
    have : (Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hC).ne'
    rw [Complex.real_smul, mul_one] at h
    push_cast
    rw [h]
    field_simp
  have h3 := norm_weilIndex hf
  rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h3
  rw [h2, h3, Complex.ofReal_one]

/-! ### Theorem 3.3 -/

/-- **GKT Theorem 3.3** (with `|β_b| = C(μ)⁻¹`): for every Schwartz–Bruhat function `φ`,
`C(μ)^{-1/2} ℱ_μ(φ ∗ f) = γ(f) ℱ_μ φ · f⁻¹`, where `(φ ∗ f)(x) = ∫ φ(z) f(x - z) dμ(z)` and `ℱ_μ` is
the Fourier transform of the bicharacter of `f`. From Weil's formula
(`bicharacterFourier_mul_bicharacterFourier`): `φ ∗ f = f · ℱ_μ(φ(-·) f)`. -/
theorem bicharacterFourier_convolution [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (hf : IsCharacterOfSecondDegree f) (μ : Measure X) [μ.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) (y : X) :
    bicharacterFourier μ (secondDegreeBicharacter f) (fun x => ∫ z, φ z * f (x - z) ∂μ) y =
      (Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) * weilIndex f) *
        (bicharacterFourier μ (secondDegreeBicharacter f) φ y * (f y)⁻¹) := by
  have he : IsSelfDualBicharacter (secondDegreeBicharacter f) := hf.isSelfDualBicharacter
  set γ := Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) * weilIndex f
  have hG : HasGaussIntegral μ f γ := hasGaussIntegral_weilIndex hf μ
  -- `ψ₀ = φ(-·) f` is Schwartz–Bruhat
  have hψ₀ : (fun z => φ (-z) * f z) ∈ schwartzBruhatSubmodule X :=
    ⟨(hφ.1.comp_continuous continuous_neg).mul hf.isLocallyConstant,
      (hφ.2.comp_homeomorph (Homeomorph.neg X)).mul_right⟩
  -- `φ ∗ f = f · ℱ ψ₀`
  have hconv : (fun x => ∫ z, φ z * f (x - z) ∂μ) =
      fun x => f x *
        bicharacterFourier μ (secondDegreeBicharacter f) (fun z => φ (-z) * f z) x := by
    funext x
    rw [bicharacterFourier, ← integral_const_mul, ← integral_neg_eq_self]
    congr 1
    funext z
    rw [sub_neg_eq_add, hf.map_add x z]
    ring
  have hfg : ∀ y u, f y * secondDegreeBicharacter f y u = (f u)⁻¹ * f (y + u) := by
    intro y u
    rw [hf.map_add y u]
    field_simp [hf.ne_zero u]
  have hW := bicharacterFourier_mul_bicharacterFourier μ he (f := f) (g := fun u => (f u)⁻¹)
    (s := id) (γ := γ) hf.continuous continuous_id hfg hG hψ₀ y
  rw [hconv, hW]
  congr 1
  -- `∫ f(y + z)⁻¹ φ(-z) f(z) dz = f(y)⁻¹ ℱ φ (y)`
  have h4 : ∫ z, (f (y + z))⁻¹ * (φ (-z) * f z) ∂μ =
      ∫ z, (f y)⁻¹ * (secondDegreeBicharacter f y (-z) * φ (-z)) ∂μ := by
    congr 1
    funext z
    have h2 : secondDegreeBicharacter f y (-z) = (secondDegreeBicharacter f y z)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← he.map_add_right, neg_add_cancel, he.map_zero_right]
    rw [hf.map_add y z, h2]
    field_simp [hf.ne_zero y, hf.ne_zero z, he.ne_zero y z]
  rw [h4, integral_const_mul, bicharacterFourier, mul_comm,
    integral_neg_eq_self (fun z => secondDegreeBicharacter f y z * φ z) μ]

/-- **GKT Corollary 3.6**: `C(μ)^{-1/2} ∫∫ φ(z) f(x - z) dz dx = γ(f) ∫ φ` (Theorem 3.3 at `0`). -/
theorem integral_convolution [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (hf : IsCharacterOfSecondDegree f) (μ : Measure X) [μ.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫ x, ∫ z, φ z * f (x - z) ∂μ ∂μ =
      (Real.sqrt (bicharacterFourierConstant μ (secondDegreeBicharacter f)) * weilIndex f) *
        ∫ x, φ x ∂μ := by
  have h := bicharacterFourier_convolution hf μ hφ 0
  have he := hf.isSelfDualBicharacter
  simp only [bicharacterFourier, he.map_zero_left, one_mul, hf.map_zero, inv_one,
    mul_one] at h
  exact h

/-! ### Proposition 3.13 (a), (d) -/

omit [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [CompactOpenExhaustion X] in
/-- A character of second degree composed with an additive homeomorphism. -/
theorem IsCharacterOfSecondDegree.comp_addEquiv {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y]
    {g : Y → ℂ} (hg : IsCharacterOfSecondDegree g) (T : X ≃ₜ+ Y) :
    IsCharacterOfSecondDegree (fun x => g (T x)) := by
  have he := hg.isSelfDualBicharacter
  have hb : secondDegreeBicharacter (fun x => g (T x)) =
      fun x y => secondDegreeBicharacter g (T x) (T y) := by
    funext x y
    simp only [secondDegreeBicharacter]
    rw [_root_.map_add T]
  refine ⟨fun x => hg.norm_eq_one _, hg.isLocallyConstant.comp_continuous T.continuous, ?_⟩
  rw [hb]
  refine ⟨fun x x' y => by rw [_root_.map_add T]; exact he.map_add_left _ _ _,
    fun x y => he.symm _ _, fun x y => he.norm_eq_one _ _,
    he.isLocallyConstant.comp_continuous (f := fun p : X × X => (T p.1, T p.2))
      (T.continuous.prodMap T.continuous), ?_, ?_⟩
  · intro U hU
    have hU' : T.symm ⁻¹' U ∈ 𝓝 (0 : Y) :=
      T.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨K, hK, hKU⟩ := he.small _ hU'
    refine ⟨T.symm '' K, hK.image T.symm.continuous, fun y hy => ?_⟩
    have := hKU (T y) fun x hx => by
      have := hy (T.symm x) ⟨x, hx, rfl⟩
      simpa using this
    simpa using this
  · intro U hU
    have hU' : T.symm ⁻¹' U ∈ 𝓝 (0 : Y) :=
      T.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨K, hK, hKU⟩ := he.big _ hU'
    refine ⟨T.symm '' K, hK.image T.symm.continuous, fun y hy => ⟨T y, hKU (T y) fun x hx => ?_,
      by simp⟩⟩
    have := hy (T.symm x) hx
    simpa using this

/-- **GKT Proposition 3.13 (a)**: the Weil index is invariant under additive homeomorphisms. -/
theorem weilIndex_comp_addEquiv {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [CompactOpenExhaustion Y] [T2Space X] [T2Space Y] {g : Y → ℂ}
    (hg : IsCharacterOfSecondDegree g) (T : X ≃ₜ+ Y) :
    weilIndex (fun x => g (T x)) = weilIndex g := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  let μ : Measure X := Measure.addHaar
  let ν : Measure Y := Measure.addHaar
  have : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hs : μ.map T = Measure.addHaarScalarFactor (μ.map T) ν • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  set s := Measure.addHaarScalarFactor (μ.map T) ν
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    exact (isOpen_univ.measure_pos (μ.map T) Set.univ_nonempty).ne' (by rw [hs]; rfl)
  have hgT := hg.comp_addEquiv T
  have h1 := HasGaussIntegral.comp_addEquiv T hs (hasGaussIntegral_weilIndex hg ν)
  have hC := bicharacterFourierConstant_pos ν (secondDegreeBicharacter g)
  have hs' : (0 : ℝ) < s := lt_of_le_of_ne s.2 (by exact_mod_cast hs0.symm)
  rw [weilIndex_eq_div_norm hgT μ h1, ← mul_assoc, ← Complex.ofReal_mul]
  exact ofReal_mul_div_norm (mul_pos hs' (Real.sqrt_pos.2 hC)) (norm_weilIndex hg)

/-! ### Proposition 3.13 (b): complex conjugation -/

omit [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [CompactOpenExhaustion X] in
/-- The complex conjugate of a character of second degree is one (GKT Proposition 3.13 (b):
`ψ̄ ∘ q = conj (ψ ∘ q)`). -/
theorem IsCharacterOfSecondDegree.conj (hf : IsCharacterOfSecondDegree f) :
    IsCharacterOfSecondDegree fun x => starRingEnd ℂ (f x) := by
  have he := hf.isSelfDualBicharacter
  have hconj1 : ∀ z : ℂ, starRingEnd ℂ z = 1 → z = 1 := fun z h => by
    simpa using congrArg (starRingEnd ℂ) h
  have he' : IsSelfDualBicharacter fun x y => starRingEnd ℂ (secondDegreeBicharacter f x y) := by
    refine ⟨fun x x' y => by rw [he.map_add_left, map_mul], fun x y => by rw [he.symm],
      fun x y => by rw [Complex.norm_conj, he.norm_eq_one],
      he.isLocallyConstant.comp (starRingEnd ℂ), fun U hU => ?_, fun U hU => ?_⟩
    · obtain ⟨K, hK, hKU⟩ := he.small U hU
      exact ⟨K, hK, fun y hy => hKU y fun x hx => hconj1 _ (hy x hx)⟩
    · obtain ⟨K, hK, hKU⟩ := he.big U hU
      exact ⟨K, hK, fun y hy => hKU y fun x hx => hconj1 _ (hy x hx)⟩
  exact IsCharacterOfSecondDegree.of_bicharacter he' (fun x => by
    rw [Complex.norm_conj, hf.norm_eq_one]) (hf.isLocallyConstant.comp (starRingEnd ℂ))
    fun x y => by rw [hf.map_add, map_mul, map_mul]

omit [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [CompactOpenExhaustion X] in
/-- The Gauss integral of `conj f` is the conjugate of that of `f`. -/
theorem HasGaussIntegral.conj [MeasurableSpace X] {μ : Measure X} {γ : ℂ}
    (h : HasGaussIntegral μ f γ) :
    HasGaussIntegral μ (fun x => starRingEnd ℂ (f x)) (starRingEnd ℂ γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hL⟩ := h K hK
  exact ⟨L, hLc, hLo, hKL, by rw [integral_conj, hL]⟩

/-- **GKT Proposition 3.13 (b)**: `γ(conj f) = conj γ(f) = γ(f)⁻¹`. -/
theorem weilIndex_conj (hf : IsCharacterOfSecondDegree f) :
    weilIndex (fun x => starRingEnd ℂ (f x)) = starRingEnd ℂ (weilIndex f) := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := Measure.addHaar
  have h := HasGaussIntegral.conj (hasGaussIntegral_weilIndex hf μ)
  rw [weilIndex_eq_div_norm hf.conj μ h, map_mul, Complex.conj_ofReal]
  exact ofReal_mul_div_norm (Real.sqrt_pos.2 (bicharacterFourierConstant_pos μ _))
    (by rw [Complex.norm_conj, norm_weilIndex hf])

theorem weilIndex_conj_eq_inv (hf : IsCharacterOfSecondDegree f) :
    weilIndex (fun x => starRingEnd ℂ (f x)) = (weilIndex f)⁻¹ := by
  rw [weilIndex_conj hf]
  have h := norm_weilIndex hf
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [mul_comm, Complex.mul_conj', h]
  simp

end WeilIndex

/-! ### Products (GKT Proposition 3.13 (d)) -/

section Pi

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

omit [DecidableEq ι] in
/-- Arbitrarily large and small compact open subgroups of a finite product. -/
theorem _root_.Langlands.HarmonicAnalysis.CompactOpenExhaustion.pi [CompactOpenExhaustion X] :
    CompactOpenExhaustion (ι → X) := by
  refine ⟨fun K hK => ?_, fun U hU => ?_⟩
  · have hL : ∀ i, ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧
        Function.eval i '' K ⊆ L :=
      fun i => CompactOpenExhaustion.exists_superset _ (hK.image (continuous_apply i))
    choose L hLc hLo hKL using hL
    refine ⟨AddSubgroup.pi Set.univ L, ?_, ?_, fun x hx => ?_⟩
    · rw [AddSubgroup.coe_pi]; exact isCompact_univ_pi hLc
    · rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => hLo i
    · rw [SetLike.mem_coe, AddSubgroup.mem_pi]
      exact fun i _ => hKL i ⟨x, hx, rfl⟩
  · rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, ht, hsub⟩ := hU
    have hL : ∀ i, ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧
        (L : Set X) ⊆ t i := fun i => CompactOpenExhaustion.exists_subset _ (ht i)
    choose L hLc hLo hLt using hL
    refine ⟨AddSubgroup.pi Set.univ L, ?_, ?_, fun x hx => hsub fun i _ => hLt i ?_⟩
    · rw [AddSubgroup.coe_pi]; exact isCompact_univ_pi hLc
    · rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => hLo i
    · rw [SetLike.mem_coe, AddSubgroup.mem_pi] at hx
      exact hx i (Set.mem_univ i)

omit [Fintype ι] [DecidableEq ι] in
private theorem isLocallyConstant_finset_prod {Z : Type*} [TopologicalSpace Z] (s : Finset ι)
    (g : ι → Z → ℂ) (hg : ∀ i, IsLocallyConstant (g i)) :
    IsLocallyConstant fun z => ∏ i ∈ s, g i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const 1
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (hg a).mul ih

/-- A product of self-dual bicharacters of `X` is a self-dual bicharacter of `ι → X`. -/
theorem _root_.Langlands.HarmonicAnalysis.IsSelfDualBicharacter.pi {e : ι → X → X → ℂ}
    (he : ∀ i, IsSelfDualBicharacter (e i)) :
    IsSelfDualBicharacter fun x y : ι → X => ∏ i, e i (x i) (y i) := by
  -- `e(single i x, y) = e_i(x, y_i)`
  have hsingle : ∀ (i : ι) (x : X) (y : ι → X),
      ∏ j, e j ((Pi.single i x : ι → X) j) (y j) = e i x (y i) := by
    intro i x y
    rw [Fintype.prod_eq_single i fun j hj => by
      rw [Pi.single_eq_of_ne hj, (he j).map_zero_left], Pi.single_eq_same]
  refine ⟨fun x x' y => ?_, fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, (he _).map_add_left, Finset.prod_mul_distrib]
  · simp only [(he _).symm (x _)]
  · simp [norm_prod, (he _).norm_eq_one]
  · refine isLocallyConstant_finset_prod Finset.univ
      (fun i (p : (ι → X) × (ι → X)) => e i (p.1 i) (p.2 i)) fun i => ?_
    exact (he i).isLocallyConstant.comp_continuous
      (f := fun p : (ι → X) × (ι → X) => (p.1 i, p.2 i)) (by fun_prop)
  · intro U hU
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, ht, hsub⟩ := hU
    have hK : ∀ i, ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, e i x y = 1) → y ∈ t i :=
      fun i => (he i).small _ (ht i)
    choose K hKc hKt using hK
    refine ⟨⋃ i, Pi.single i '' K i, isCompact_iUnion fun i => (hKc i).image
      (continuous_single (A := fun _ : ι => X) i), fun y hy => hsub fun i _ => hKt i (y i)
      fun x hx => ?_⟩
    have := hy (Pi.single i x) (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
    rwa [hsingle] at this
  · intro U hU
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, ht, hsub⟩ := hU
    have hK : ∀ i, ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ t i, e i x y = 1) → y ∈ K :=
      fun i => (he i).big _ (ht i)
    choose K hKc hKt using hK
    refine ⟨Set.univ.pi K, isCompact_univ_pi hKc, fun y hy i _ => hKt i (y i) fun x hx => ?_⟩
    have hmem : (Pi.single i x : ι → X) ∈ U := hsub fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using hx
      · rw [Pi.single_eq_of_ne hj]; exact mem_of_mem_nhds (ht j)
    have := hy _ hmem
    rwa [hsingle] at this

/-- A product of characters of second degree on `X` is one on `ι → X` (GKT Proposition 3.13 (d),
the orthogonal direct sum). -/
theorem IsCharacterOfSecondDegree.pi {f : ι → X → ℂ} (hf : ∀ i, IsCharacterOfSecondDegree (f i)) :
    IsCharacterOfSecondDegree (fun x : ι → X => ∏ i, f i (x i)) := by
  have hb : secondDegreeBicharacter (fun x : ι → X => ∏ i, f i (x i)) =
      fun x y => ∏ i, secondDegreeBicharacter (f i) (x i) (y i) := by
    funext x y
    simp only [secondDegreeBicharacter, Pi.add_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      Finset.prod_inv_distrib]
  refine ⟨fun x => by simp [norm_prod, (hf _).norm_eq_one],
    isLocallyConstant_finset_prod Finset.univ (fun i (x : ι → X) => f i (x i))
      fun i => (hf i).isLocallyConstant.comp_continuous (continuous_apply i), ?_⟩
  rw [hb]
  exact IsSelfDualBicharacter.pi fun i => (hf i).isSelfDualBicharacter

variable [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [CompactOpenExhaustion X] [T2Space X]

/-- **GKT Proposition 3.13 (d)**: the Weil index of a product of characters of second degree is
the product of their Weil indices. -/
theorem weilIndex_pi {f : ι → X → ℂ} (hf : ∀ i, IsCharacterOfSecondDegree (f i)) :
    weilIndex (fun x : ι → X => ∏ i, f i (x i)) = ∏ i, weilIndex (f i) := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have : CompactOpenExhaustion (ι → X) := CompactOpenExhaustion.pi
  let μ : Measure X := Measure.addHaar
  have h := HasGaussIntegral.pi (μ := μ) fun i => hasGaussIntegral_weilIndex (hf i) μ
  rw [weilIndex_eq_div_norm (IsCharacterOfSecondDegree.pi hf) (Measure.pi fun _ : ι => μ) h,
    Finset.prod_mul_distrib, ← Complex.ofReal_prod]
  refine ofReal_mul_div_norm (Finset.prod_pos fun i _ => Real.sqrt_pos.2
    (bicharacterFourierConstant_pos μ _)) ?_
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => norm_weilIndex (hf i)

end Pi

/-! ### Orthogonal sums of two spaces (GKT Proposition 3.13 (d), (e)) -/

section Prod

variable {X Y : Type*} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]

/-- Arbitrarily large and small compact open subgroups of a product. -/
theorem _root_.Langlands.HarmonicAnalysis.CompactOpenExhaustion.prod [CompactOpenExhaustion X]
    [CompactOpenExhaustion Y] : CompactOpenExhaustion (X × Y) := by
  refine ⟨fun K hK => ?_, fun U hU => ?_⟩
  · obtain ⟨L₁, hL₁c, hL₁o, hK₁⟩ :=
      CompactOpenExhaustion.exists_superset _
        (hK.image (continuous_fst : Continuous (Prod.fst : X × Y → X)))
    obtain ⟨L₂, hL₂c, hL₂o, hK₂⟩ :=
      CompactOpenExhaustion.exists_superset _
        (hK.image (continuous_snd : Continuous (Prod.snd : X × Y → Y)))
    refine ⟨L₁.prod L₂, ?_, ?_, fun p hp => ⟨hK₁ ⟨p, hp, rfl⟩, hK₂ ⟨p, hp, rfl⟩⟩⟩
    · rw [AddSubgroup.coe_prod]; exact hL₁c.prod hL₂c
    · rw [AddSubgroup.coe_prod]; exact hL₁o.prod hL₂o
  · obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1
      (show U ∈ 𝓝 ((0 : X), (0 : Y)) by rwa [Prod.mk_zero_zero])
    obtain ⟨L₁, hL₁c, hL₁o, hL₁⟩ := CompactOpenExhaustion.exists_subset U₁ hU₁
    obtain ⟨L₂, hL₂c, hL₂o, hL₂⟩ := CompactOpenExhaustion.exists_subset U₂ hU₂
    refine ⟨L₁.prod L₂, ?_, ?_, fun p hp => hsub ⟨hL₁ hp.1, hL₂ hp.2⟩⟩
    · rw [AddSubgroup.coe_prod]; exact hL₁c.prod hL₂c
    · rw [AddSubgroup.coe_prod]; exact hL₁o.prod hL₂o

/-- A product of self-dual bicharacters is a self-dual bicharacter of `X × Y`. -/
theorem _root_.Langlands.HarmonicAnalysis.IsSelfDualBicharacter.prod {e₁ : X → X → ℂ}
    {e₂ : Y → Y → ℂ} (he₁ : IsSelfDualBicharacter e₁) (he₂ : IsSelfDualBicharacter e₂) :
    IsSelfDualBicharacter fun p q : X × Y => e₁ p.1 q.1 * e₂ p.2 q.2 := by
  refine ⟨fun p p' q => ?_, fun p q => ?_, fun p q => ?_, ?_, fun U hU => ?_, fun U hU => ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add, he₁.map_add_left, he₂.map_add_left]; ring
  · rw [he₁.symm, he₂.symm]
  · rw [norm_mul, he₁.norm_eq_one, he₂.norm_eq_one, one_mul]
  · exact (he₁.isLocallyConstant.comp_continuous
      (f := fun r : (X × Y) × (X × Y) => (r.1.1, r.2.1)) (by fun_prop)).mul
      (he₂.isLocallyConstant.comp_continuous
        (f := fun r : (X × Y) × (X × Y) => (r.1.2, r.2.2)) (by fun_prop))
  · obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1
      (show U ∈ 𝓝 ((0 : X), (0 : Y)) by rwa [Prod.mk_zero_zero])
    obtain ⟨K₁, hK₁, hK₁U⟩ := he₁.small U₁ hU₁
    obtain ⟨K₂, hK₂, hK₂U⟩ := he₂.small U₂ hU₂
    refine ⟨(fun x => (x, (0 : Y))) '' K₁ ∪ (fun y => ((0 : X), y)) '' K₂,
      (hK₁.image (by fun_prop)).union (hK₂.image (by fun_prop)), fun q hq => hsub ⟨?_, ?_⟩⟩
    · refine hK₁U q.1 fun x hx => ?_
      have := hq _ (Or.inl ⟨x, hx, rfl⟩)
      rwa [he₂.map_zero_left, mul_one] at this
    · refine hK₂U q.2 fun y hy => ?_
      have := hq _ (Or.inr ⟨y, hy, rfl⟩)
      rwa [he₁.map_zero_left, one_mul] at this
  · obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1
      (show U ∈ 𝓝 ((0 : X), (0 : Y)) by rwa [Prod.mk_zero_zero])
    obtain ⟨K₁, hK₁, hK₁U⟩ := he₁.big U₁ hU₁
    obtain ⟨K₂, hK₂, hK₂U⟩ := he₂.big U₂ hU₂
    refine ⟨K₁ ×ˢ K₂, hK₁.prod hK₂, fun q hq => ⟨hK₁U q.1 fun x hx => ?_, hK₂U q.2 fun y hy => ?_⟩⟩
    · have := hq (x, 0) (hsub ⟨hx, mem_of_mem_nhds hU₂⟩)
      rwa [he₂.map_zero_left, mul_one] at this
    · have := hq (0, y) (hsub ⟨mem_of_mem_nhds hU₁, hy⟩)
      rwa [he₁.map_zero_left, one_mul] at this

/-- The product of characters of second degree on `X` and `Y` is one on `X × Y` (the orthogonal
direct sum, GKT Proposition 3.13 (d)). -/
theorem IsCharacterOfSecondDegree.prod {f₁ : X → ℂ} {f₂ : Y → ℂ}
    (hf₁ : IsCharacterOfSecondDegree f₁) (hf₂ : IsCharacterOfSecondDegree f₂) :
    IsCharacterOfSecondDegree fun p : X × Y => f₁ p.1 * f₂ p.2 := by
  have hb : secondDegreeBicharacter (fun p : X × Y => f₁ p.1 * f₂ p.2) =
      fun p q => secondDegreeBicharacter f₁ p.1 q.1 * secondDegreeBicharacter f₂ p.2 q.2 := by
    funext p q
    simp only [secondDegreeBicharacter, Prod.fst_add, Prod.snd_add, mul_inv]
    ring
  refine ⟨fun p => by rw [norm_mul, hf₁.norm_eq_one, hf₂.norm_eq_one, one_mul],
    (hf₁.isLocallyConstant.comp_continuous continuous_fst).mul
      (hf₂.isLocallyConstant.comp_continuous continuous_snd), ?_⟩
  rw [hb]
  exact hf₁.isSelfDualBicharacter.prod hf₂.isSelfDualBicharacter

/-- Gauss integrals of products for a product measure. -/
theorem HasGaussIntegral.prod [MeasurableSpace X] [MeasurableSpace Y] {μ₁ : Measure X}
    {μ₂ : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] {f₁ : X → ℂ} {f₂ : Y → ℂ} {γ₁ γ₂ : ℂ}
    (h₁ : HasGaussIntegral μ₁ f₁ γ₁) (h₂ : HasGaussIntegral μ₂ f₂ γ₂) :
    HasGaussIntegral (μ₁.prod μ₂) (fun p => f₁ p.1 * f₂ p.2) (γ₁ * γ₂) := by
  intro K hK
  obtain ⟨L₁, hL₁c, hL₁o, hK₁, hL₁⟩ :=
    h₁ _ (hK.image (continuous_fst : Continuous (Prod.fst : X × Y → X)))
  obtain ⟨L₂, hL₂c, hL₂o, hK₂, hL₂⟩ :=
    h₂ _ (hK.image (continuous_snd : Continuous (Prod.snd : X × Y → Y)))
  refine ⟨L₁.prod L₂, ?_, ?_, fun p hp => ⟨hK₁ ⟨p, hp, rfl⟩, hK₂ ⟨p, hp, rfl⟩⟩, ?_⟩
  · rw [AddSubgroup.coe_prod]; exact hL₁c.prod hL₂c
  · rw [AddSubgroup.coe_prod]; exact hL₁o.prod hL₂o
  · rw [AddSubgroup.coe_prod, ← Measure.prod_restrict, integral_prod_mul, hL₁, hL₂]

variable [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [CompactOpenExhaustion X] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [CompactOpenExhaustion Y]

/-- **GKT Proposition 3.13 (d)**: the Weil index of an orthogonal direct sum is the product of the
Weil indices. -/
theorem weilIndex_prod {f₁ : X → ℂ} {f₂ : Y → ℂ} (hf₁ : IsCharacterOfSecondDegree f₁)
    (hf₂ : IsCharacterOfSecondDegree f₂) :
    weilIndex (fun p : X × Y => f₁ p.1 * f₂ p.2) = weilIndex f₁ * weilIndex f₂ := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  have : CompactOpenExhaustion (X × Y) := CompactOpenExhaustion.prod
  let μ₁ : Measure X := Measure.addHaar
  let μ₂ : Measure Y := Measure.addHaar
  have h := HasGaussIntegral.prod (hasGaussIntegral_weilIndex hf₁ μ₁)
    (hasGaussIntegral_weilIndex hf₂ μ₂)
  rw [weilIndex_eq_div_norm (hf₁.prod hf₂) (μ₁.prod μ₂) h]
  have e : (Real.sqrt (bicharacterFourierConstant μ₁ (secondDegreeBicharacter f₁)) : ℂ) *
      weilIndex f₁ * ((Real.sqrt (bicharacterFourierConstant μ₂ (secondDegreeBicharacter f₂)) : ℂ) *
        weilIndex f₂) =
      ((Real.sqrt (bicharacterFourierConstant μ₁ (secondDegreeBicharacter f₁)) *
        Real.sqrt (bicharacterFourierConstant μ₂ (secondDegreeBicharacter f₂)) : ℝ) : ℂ) *
        (weilIndex f₁ * weilIndex f₂) := by push_cast; ring
  rw [e]
  refine ofReal_mul_div_norm (mul_pos (Real.sqrt_pos.2 (bicharacterFourierConstant_pos _ _))
    (Real.sqrt_pos.2 (bicharacterFourierConstant_pos _ _))) ?_
  rw [norm_mul, norm_weilIndex hf₁, norm_weilIndex hf₂, one_mul]

/-- **GKT Proposition 3.13 (e)**: `γ(f ⊕ conj f) = 1`; for a quadratic form, `(Y, r) ⊕ (Y, -r)` has
Weil index one. -/
theorem weilIndex_prod_conj {f : X → ℂ} (hf : IsCharacterOfSecondDegree f) :
    weilIndex (fun p : X × X => f p.1 * starRingEnd ℂ (f p.2)) = 1 := by
  rw [weilIndex_prod hf hf.conj, weilIndex_conj hf, Complex.mul_conj', norm_weilIndex hf]
  simp

end Prod

/-! ### Quadratic forms over a nonarchimedean local field -/

section QuadraticForm

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V]

/-- A quadratic form on a finite-dimensional space with its module topology is continuous. -/
theorem continuous_quadraticForm (q : QuadraticForm F V) : Continuous q := by
  obtain ⟨B, rfl⟩ := LinearMap.BilinMap.toQuadraticMap_surjective q
  have := IsModuleTopology.continuous_bilinear_of_finite_left B
  exact this.comp (continuous_id.prodMk continuous_id)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F V]
  [TopologicalSpace V] [IsModuleTopology F V] in
/-- The bicharacter of `x ↦ ψ(q x)` is `ψ ∘ polar q` (GKT (3.6)). -/
theorem secondDegreeBicharacter_quadraticForm (ψ : AddChar F ℂ) (q : QuadraticForm F V) :
    secondDegreeBicharacter (fun x => ψ (q x)) = fun x y => ψ (QuadraticMap.polar q x y) := by
  funext x y
  simp only [secondDegreeBicharacter, QuadraticMap.polar, ← AddChar.map_neg_eq_inv,
    ← AddChar.map_add_eq_mul]
  ring_nf

/-- **`ψ ∘ q` is a character of second degree** (GKT 3.1.3) for a non-trivial continuous unitary
character `ψ` and a quadratic form `q` whose polar form is non-degenerate; its bicharacter is
`ψ ∘ polar q`, and its Weil index is the book's `γ(ψ ∘ q)` (Definition 3.4 with `q = ½ q_b`). -/
theorem isCharacterOfSecondDegree_quadraticForm {ψ : AddChar F ℂ} (hψ : Continuous ψ)
    (hn : ∀ t, ‖ψ t‖ = 1) (h1 : ψ ≠ 1) (q : QuadraticForm F V)
    (hq : (QuadraticMap.polarBilin q).SeparatingLeft) :
    IsCharacterOfSecondDegree (fun x => ψ (q x)) := by
  have he := isSelfDualBicharacter_of_symm hψ hn h1 (QuadraticMap.polarBilin q)
    (fun x y => by simp [QuadraticMap.polar_comm]) fun y hy => hq y fun x => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      simpa using hy x
  refine ⟨fun x => hn _, (isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous
    (continuous_quadraticForm q), ?_⟩
  rw [secondDegreeBicharacter_quadraticForm]
  simpa using he

end QuadraticForm

end Langlands.Theta
