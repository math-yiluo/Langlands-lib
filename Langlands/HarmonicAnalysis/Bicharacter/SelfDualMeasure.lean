import Langlands.HarmonicAnalysis.Bicharacter.Fourier

/-!
# Dual and self-dual Haar measures of a self-dual bicharacter

GKT Appendix 1.A (Theorem 1.37, Remark 1.38, Proposition 1.39, Definition 1.40, pp. 43–45) in the
self-dual case `H = G` with a symmetric pairing: for a self-dual bicharacter `e` on `X` and a Haar
measure `μ`, the Fourier transform `ℱ_μ φ (x) = ∫ e(x, y) φ(y) dμ(y)` applied twice is
`bicharacterFourierConstant μ e` times the reflection (`bicharacterFourier_bicharacterFourier_eq`).

* `bicharacterDualMeasure μ e = C(μ)⁻¹ μ` is the dual Haar measure: `ℱ_{μ'} ℱ_μ φ = φ(-·)`
  (`bicharacterFourier_bicharacterDualMeasure`), it is the only Haar measure with this property
  (`eq_bicharacterDualMeasure`), `ℱ_μ` is an isometry `L²(μ) → L²(μ')`
  (`lintegral_enorm_bicharacterFourier_sq_bicharacterDualMeasure`); `(rμ)' = r⁻¹ μ'` and
  `μ'' = μ` (Remark 1.38).
* `selfDualMeasure e` is the unique Haar measure dual to itself (Proposition 1.39,
  Definition 1.40): `selfDualMeasure e = C(μ)^{-1/2} μ` for every Haar measure `μ`
  (`selfDualMeasure_eq_smul`); `ℱ ℱ φ = φ(-·)` and `ℱ` is an isometry for it.

`C(rμ) = r² C(μ)` (`bicharacterFourierConstant_smul`) because `ℱ_{rμ} = r ℱ_μ`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarmonicAnalysis

section Defs

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]

/-- The constant of Fourier inversion for the bicharacter `e` and the measure `μ`: the `C > 0`
with `ℱ_μ ℱ_μ φ (x) = C φ(-x)` for every Schwartz–Bruhat function `φ`
(`bicharacterFourier_bicharacterFourier_eq`; `1` when there is none). -/
def bicharacterFourierConstant (μ : Measure X) (e : X → X → ℂ) : ℝ :=
  open Classical in
  if h : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x) then h.choose
  else 1

/-- The dual Haar measure of `μ` for the bicharacter `e` (GKT Theorem 1.37 (b) for `H = G`):
`C(μ)⁻¹ μ`, the measure `μ'` with `ℱ_{μ'} ℱ_μ φ = φ(-·)`. -/
def bicharacterDualMeasure (μ : Measure X) (e : X → X → ℂ) : Measure X :=
  (bicharacterFourierConstant μ e)⁻¹.toNNReal • μ

/-- **The self-dual Haar measure** of the bicharacter `e` (GKT Proposition 1.39,
Definition 1.40): the Haar measure `μ` with `ℱ_μ ℱ_μ φ = φ(-·)` for every Schwartz–Bruhat
function `φ`; it exists and is unique for a self-dual bicharacter (`eq_selfDualMeasure_iff`). -/
def selfDualMeasure (e : X → X → ℂ) : Measure X :=
  open Classical in
  if h : ∃ μ : Measure X, μ.IsAddHaarMeasure ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = φ (-x) then h.choose
  else 0

theorem bicharacterFourierConstant_pos (μ : Measure X) (e : X → X → ℂ) :
    0 < bicharacterFourierConstant μ e := by
  classical
  unfold bicharacterFourierConstant
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos

omit [AddCommGroup X] [TopologicalSpace X] in
/-- `ℱ_{rμ} = r ℱ_μ`. -/
theorem bicharacterFourier_smul_measure (μ : Measure X) (e : X → X → ℂ) (r : ℝ≥0) (φ : X → ℂ)
    (x : X) :
    bicharacterFourier (r • μ) e φ x = ((r : ℝ) : ℂ) * bicharacterFourier μ e φ x := by
  simp only [bicharacterFourier, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

omit [AddCommGroup X] [TopologicalSpace X] in
/-- `ℱ_μ (c φ) = c ℱ_μ φ`. -/
theorem bicharacterFourier_const_mul (μ : Measure X) (e : X → X → ℂ) (c : ℂ) (φ : X → ℂ)
    (x : X) :
    bicharacterFourier μ e (fun y => c * φ y) x = c * bicharacterFourier μ e φ x := by
  simp only [bicharacterFourier, mul_left_comm (e x _) c]
  exact integral_const_mul c _

end Defs

section Haar

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X]
  [MeasurableSpace X] [BorelSpace X] {e : X → X → ℂ}

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- A Schwartz–Bruhat function with value `1` at `0`: the indicator of a compact open
subgroup. -/
theorem exists_mem_schwartzBruhatSubmodule_apply_zero :
    ∃ φ ∈ schwartzBruhatSubmodule X, φ 0 = 1 := by
  obtain ⟨L, hLc, hLo, -⟩ := CompactOpenExhaustion.exists_superset (∅ : Set X) isCompact_empty
  exact ⟨_, indicator_one_mem_schwartzBruhatSubmodule L hLc hLo,
    Set.indicator_of_mem L.zero_mem _⟩

omit [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
/-- The constant of Fourier inversion is the `C` of any inversion formula
`ℱ_μ ℱ_μ φ = C φ(-·)`. -/
theorem bicharacterFourierConstant_eq {μ : Measure X} {C : ℝ} (hC : 0 < C)
    (h : ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x)) :
    bicharacterFourierConstant μ e = C := by
  classical
  have hex : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = (C : ℂ) * φ (-x) := ⟨C, hC, h⟩
  rw [bicharacterFourierConstant, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨φ, hφ, h0⟩ := exists_mem_schwartzBruhatSubmodule_apply_zero (X := X)
  have h1 := hex.choose_spec.2 φ hφ 0
  have h2 := h φ hφ 0
  rw [neg_zero, h0, mul_one] at h1 h2
  exact_mod_cast h1.symm.trans h2

/-- **Fourier inversion** for a self-dual bicharacter and a Haar measure `μ`:
`ℱ_μ ℱ_μ φ (x) = C(μ) φ(-x)`. -/
theorem bicharacterFourier_bicharacterFourier_eq (he : IsSelfDualBicharacter e) (μ : Measure X)
    [μ.IsAddHaarMeasure] {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) (x : X) :
    bicharacterFourier μ e (bicharacterFourier μ e φ) x =
      (bicharacterFourierConstant μ e : ℂ) * φ (-x) := by
  obtain ⟨C, hC, h⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ he
  rw [bicharacterFourierConstant_eq hC h]
  exact h φ hφ x

/-- `C(rμ) = r² C(μ)`. -/
theorem bicharacterFourierConstant_smul (he : IsSelfDualBicharacter e) (μ : Measure X)
    [μ.IsAddHaarMeasure] {r : ℝ≥0} (hr : r ≠ 0) :
    bicharacterFourierConstant (r • μ) e = (r : ℝ) ^ 2 * bicharacterFourierConstant μ e := by
  have hr' : (0 : ℝ) < r := lt_of_le_of_ne r.2 (by exact_mod_cast hr.symm)
  refine bicharacterFourierConstant_eq (by have := bicharacterFourierConstant_pos μ e; positivity)
    fun φ hφ x => ?_
  have h1 : bicharacterFourier (r • μ) e φ = fun y => ((r : ℝ) : ℂ) * bicharacterFourier μ e φ y :=
    funext fun y => bicharacterFourier_smul_measure μ e r φ y
  rw [bicharacterFourier_smul_measure, h1, bicharacterFourier_const_mul,
    bicharacterFourier_bicharacterFourier_eq he μ hφ x]
  push_cast
  ring

/-! ### The dual measure (Theorem 1.37 and Remark 1.38 for `H = G`) -/

/-- **The dual measure inverts the Fourier transform** (GKT Theorem 1.37 (d)):
`ℱ_{μ'} ℱ_μ φ = φ(-·)` for `μ' = bicharacterDualMeasure μ e`. -/
theorem bicharacterFourier_bicharacterDualMeasure (he : IsSelfDualBicharacter e)
    (μ : Measure X) [μ.IsAddHaarMeasure] {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X)
    (x : X) :
    bicharacterFourier (bicharacterDualMeasure μ e) e (bicharacterFourier μ e φ) x = φ (-x) := by
  have hC := bicharacterFourierConstant_pos μ e
  rw [bicharacterDualMeasure, bicharacterFourier_smul_measure,
    bicharacterFourier_bicharacterFourier_eq he μ hφ x, Real.coe_toNNReal _ (inv_nonneg.2 hC.le)]
  have hC' : ((bicharacterFourierConstant μ e : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  push_cast
  field_simp

/-- **The dual measure is unique** (GKT Theorem 1.37 (b)): a Haar measure `ν` with
`ℱ_ν ℱ_μ φ = φ(-·)` for all Schwartz–Bruhat functions `φ` is `bicharacterDualMeasure μ e`. -/
theorem eq_bicharacterDualMeasure (he : IsSelfDualBicharacter e) (μ : Measure X)
    [μ.IsAddHaarMeasure] {ν : Measure X} [ν.IsAddHaarMeasure]
    (h : ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier ν e (bicharacterFourier μ e φ) x = φ (-x)) :
    ν = bicharacterDualMeasure μ e := by
  have hs : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  set s := Measure.addHaarScalarFactor ν μ
  obtain ⟨φ, hφ, h0⟩ := exists_mem_schwartzBruhatSubmodule_apply_zero (X := X)
  have h1 := h φ hφ 0
  rw [hs, bicharacterFourier_smul_measure, bicharacterFourier_bicharacterFourier_eq he μ hφ,
    neg_zero, h0, mul_one] at h1
  have hC := bicharacterFourierConstant_pos μ e
  have h2 : (s : ℝ) = (bicharacterFourierConstant μ e)⁻¹ := by
    have h3 : (s : ℝ) * bicharacterFourierConstant μ e = 1 := by exact_mod_cast h1
    field_simp
    linarith
  rw [hs, bicharacterDualMeasure]
  congr 1
  exact NNReal.eq (by rw [h2, Real.coe_toNNReal _ (inv_nonneg.2 hC.le)])

/-- The dual of `rμ` is `r⁻¹` times the dual of `μ` (GKT Remark 1.38). -/
theorem bicharacterDualMeasure_smul (he : IsSelfDualBicharacter e) (μ : Measure X)
    [μ.IsAddHaarMeasure] {r : ℝ≥0} (hr : r ≠ 0) :
    bicharacterDualMeasure (r • μ) e = r⁻¹ • bicharacterDualMeasure μ e := by
  have hC := bicharacterFourierConstant_pos μ e
  have hr' : (0 : ℝ) < r := lt_of_le_of_ne r.2 (by exact_mod_cast hr.symm)
  rw [bicharacterDualMeasure, bicharacterDualMeasure, bicharacterFourierConstant_smul he μ hr,
    smul_smul, smul_smul]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_inv]
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  field_simp

/-- The dual of the dual measure is the measure (GKT Remark 1.38: `μ` and `μ'` are dual to each
other). -/
theorem bicharacterDualMeasure_bicharacterDualMeasure (he : IsSelfDualBicharacter e)
    (μ : Measure X) [μ.IsAddHaarMeasure] :
    bicharacterDualMeasure (bicharacterDualMeasure μ e) e = μ := by
  have hC := bicharacterFourierConstant_pos μ e
  have hr : (bicharacterFourierConstant μ e)⁻¹.toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero] using hC
  have hd : bicharacterDualMeasure μ e = (bicharacterFourierConstant μ e)⁻¹.toNNReal • μ := rfl
  rw [hd, bicharacterDualMeasure_smul he μ hr, hd, smul_smul, inv_mul_cancel₀ hr, one_smul]

omit [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [CompactOpenExhaustion X] [BorelSpace X] in
private theorem lintegral_enorm_sq_toNNReal_smul (μ : Measure X) {C : ℝ} (hC : 0 < C)
    (f : X → ℂ) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(C⁻¹.toNNReal • μ)) * ENNReal.ofReal C = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, mul_comm, ← mul_assoc]
  have : ENNReal.ofReal C * ((C⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.ofReal, ← ENNReal.coe_mul, ← Real.toNNReal_mul hC.le, mul_inv_cancel₀ hC.ne',
      Real.toNNReal_one, ENNReal.coe_one]
  rw [this, one_mul]

/-- **Plancherel's formula for the dual measure** (GKT Theorem 1.37 (b)): `ℱ_μ` is an isometry
from `L²(μ)` to `L²(μ')`, `μ' = bicharacterDualMeasure μ e`. -/
theorem lintegral_enorm_bicharacterFourier_sq_bicharacterDualMeasure
    (he : IsSelfDualBicharacter e) (μ : Measure X) [μ.IsAddHaarMeasure] {φ : X → ℂ}
    (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫⁻ x, ‖bicharacterFourier μ e φ x‖ₑ ^ 2 ∂(bicharacterDualMeasure μ e) =
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  have hC := bicharacterFourierConstant_pos μ e
  have hpl := lintegral_enorm_bicharacterFourier_sq μ he _ hC
    (fun φ hφ x => bicharacterFourier_bicharacterFourier_eq he μ hφ x) hφ
  have h := lintegral_enorm_sq_toNNReal_smul μ hC (bicharacterFourier μ e φ)
  rw [hpl] at h
  rw [bicharacterDualMeasure]
  have hne : ENNReal.ofReal (bicharacterFourierConstant μ e) ≠ 0 := by simpa using hC
  have hnt : ENNReal.ofReal (bicharacterFourierConstant μ e) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [mul_comm] at h
  exact (ENNReal.mul_right_inj hne hnt).1 h

/-! ### The self-dual measure (Proposition 1.39, Definition 1.40) -/

omit [LocallyCompactSpace X] [SecondCountableTopology X] [CompactOpenExhaustion X] in
private theorem isAddHaarMeasure_toNNReal_smul (μ : Measure X) [μ.IsAddHaarMeasure] {c : ℝ}
    (hc : 0 < c) : (c.toNNReal • μ).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.nnreal_smul μ (by simpa [Real.toNNReal_eq_zero] using hc)

/-- Two Haar measures with Fourier constant `1` are equal. -/
private theorem eq_of_bicharacterFourierConstant_eq_one (he : IsSelfDualBicharacter e)
    {μ ν : Measure X} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (hμ : bicharacterFourierConstant μ e = 1) (hν : bicharacterFourierConstant ν e = 1) :
    ν = μ := by
  have hs : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  set s := Measure.addHaarScalarFactor ν μ
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne' (by rw [hs]; rfl)
  have h1 := bicharacterFourierConstant_smul he μ hs0
  rw [← hs, hν, hμ, mul_one] at h1
  have h2 : (s : ℝ) = 1 := (pow_eq_one_iff_of_nonneg s.2 two_ne_zero).1 h1.symm
  rw [hs, show s = 1 from NNReal.eq h2, one_smul]

/-- The Haar measure `C(μ)^{-1/2} μ` has Fourier constant `1`. -/
private theorem bicharacterFourierConstant_sqrt_smul (he : IsSelfDualBicharacter e)
    (μ : Measure X) [μ.IsAddHaarMeasure] :
    bicharacterFourierConstant ((Real.sqrt (bicharacterFourierConstant μ e))⁻¹.toNNReal • μ) e =
      1 := by
  have hC := bicharacterFourierConstant_pos μ e
  have hs : 0 < (Real.sqrt (bicharacterFourierConstant μ e))⁻¹ := by positivity
  rw [bicharacterFourierConstant_smul he μ (by simpa [Real.toNNReal_eq_zero] using hs),
    Real.coe_toNNReal _ hs.le, inv_pow, Real.sq_sqrt hC.le, inv_mul_cancel₀ hC.ne']

/-- **The self-dual measure** is `C(μ)^{-1/2} μ` for every Haar measure `μ` (GKT Proposition 1.39:
it is dual to itself, and it is the only such Haar measure). -/
theorem selfDualMeasure_eq_smul (he : IsSelfDualBicharacter e) (μ : Measure X)
    [μ.IsAddHaarMeasure] :
    selfDualMeasure e = (Real.sqrt (bicharacterFourierConstant μ e))⁻¹.toNNReal • μ := by
  classical
  have hC := bicharacterFourierConstant_pos μ e
  set ν := (Real.sqrt (bicharacterFourierConstant μ e))⁻¹.toNNReal • μ with hνd
  have : ν.IsAddHaarMeasure := isAddHaarMeasure_toNNReal_smul μ (by positivity)
  have hν1 := bicharacterFourierConstant_sqrt_smul he μ
  have hex : ∃ μ : Measure X, μ.IsAddHaarMeasure ∧ ∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = φ (-x) :=
    ⟨ν, this, fun φ hφ x => by
      rw [bicharacterFourier_bicharacterFourier_eq he ν hφ x, hν1, Complex.ofReal_one,
        one_mul]⟩
  rw [selfDualMeasure, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h3 : bicharacterFourierConstant hex.choose e = 1 :=
    bicharacterFourierConstant_eq one_pos fun φ hφ x => by
      rw [h2 φ hφ x, Complex.ofReal_one, one_mul]
  exact eq_of_bicharacterFourierConstant_eq_one he hν1 h3

/-- The self-dual measure is a Haar measure. -/
theorem isAddHaarMeasure_selfDualMeasure (he : IsSelfDualBicharacter e) :
    (selfDualMeasure e).IsAddHaarMeasure := by
  rw [selfDualMeasure_eq_smul he Measure.addHaar]
  exact isAddHaarMeasure_toNNReal_smul _ (by
    have := bicharacterFourierConstant_pos (Measure.addHaar : Measure X) e
    positivity)

/-- The self-dual measure has Fourier constant `1`. -/
theorem bicharacterFourierConstant_selfDualMeasure (he : IsSelfDualBicharacter e) :
    bicharacterFourierConstant (selfDualMeasure e) e = 1 := by
  rw [selfDualMeasure_eq_smul he Measure.addHaar]
  exact bicharacterFourierConstant_sqrt_smul he _

/-- **Fourier inversion for the self-dual measure**: `ℱ ℱ φ = φ(-·)`. -/
theorem bicharacterFourier_bicharacterFourier_selfDualMeasure (he : IsSelfDualBicharacter e)
    {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) (x : X) :
    bicharacterFourier (selfDualMeasure e) e (bicharacterFourier (selfDualMeasure e) e φ) x =
      φ (-x) := by
  have := isAddHaarMeasure_selfDualMeasure he
  rw [bicharacterFourier_bicharacterFourier_eq he _ hφ x,
    bicharacterFourierConstant_selfDualMeasure he, Complex.ofReal_one, one_mul]

/-- **Uniqueness of the self-dual measure** (GKT Proposition 1.39): a Haar measure `μ` satisfies
`ℱ_μ ℱ_μ φ = φ(-·)` for all Schwartz–Bruhat functions `φ` if and only if it is the self-dual
measure. -/
theorem eq_selfDualMeasure_iff (he : IsSelfDualBicharacter e) (μ : Measure X)
    [μ.IsAddHaarMeasure] :
    (∀ φ ∈ schwartzBruhatSubmodule X, ∀ x,
      bicharacterFourier μ e (bicharacterFourier μ e φ) x = φ (-x)) ↔ μ = selfDualMeasure e := by
  have := isAddHaarMeasure_selfDualMeasure he
  constructor
  · intro h
    have h1 : bicharacterFourierConstant μ e = 1 :=
      bicharacterFourierConstant_eq one_pos fun φ hφ x => by
        rw [h φ hφ x, Complex.ofReal_one, one_mul]
    exact eq_of_bicharacterFourierConstant_eq_one he
      (bicharacterFourierConstant_selfDualMeasure he) h1
  · rintro rfl
    exact fun φ hφ x => bicharacterFourier_bicharacterFourier_selfDualMeasure he hφ x

/-- The self-dual measure is its own dual measure (GKT Definition 1.40). -/
theorem bicharacterDualMeasure_selfDualMeasure (he : IsSelfDualBicharacter e) :
    bicharacterDualMeasure (selfDualMeasure e) e = selfDualMeasure e := by
  rw [bicharacterDualMeasure, bicharacterFourierConstant_selfDualMeasure he, inv_one,
    Real.toNNReal_one, one_smul]

/-- **Plancherel's formula for the self-dual measure**: `ℱ` is an isometry of `L²`. -/
theorem lintegral_enorm_bicharacterFourier_sq_selfDualMeasure (he : IsSelfDualBicharacter e)
    {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) :
    ∫⁻ x, ‖bicharacterFourier (selfDualMeasure e) e φ x‖ₑ ^ 2 ∂(selfDualMeasure e) =
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(selfDualMeasure e) := by
  have := isAddHaarMeasure_selfDualMeasure he
  have h := lintegral_enorm_bicharacterFourier_sq_bicharacterDualMeasure he
    (selfDualMeasure e) hφ
  rwa [bicharacterDualMeasure_selfDualMeasure he] at h

end Haar

end Langlands.HarmonicAnalysis
