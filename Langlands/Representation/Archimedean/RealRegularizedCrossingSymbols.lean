import Langlands.Representation.Archimedean.RealInducedSwapRegularizedFamily

/-! # Reciprocal regularized real crossing symbols along affine lines -/

noncomputable section

open Filter Set
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealRegularizedCrossingSymbols

open RealBlockMultiplier
open RealInducedSwapRegularizedFamily (ValidChoice multiplier)

/-- Remove the unique denominator that vanishes at the central parameter, when it exists. -/
def choice (ν : ℂ) (ε : ℤ) : Option ℕ := by
  classical
  exact if h : ∃ r : ℕ, ν = -((ε : ℂ) + 2 * r + 1) then some h.choose else none

theorem validChoice (ν : ℂ) (ε : ℤ) : ValidChoice ν ε (choice ν ε) := by
  classical
  unfold choice
  split_ifs with h
  · exact h.choose_spec
  · exact fun r hr => h ⟨r, hr⟩

/-- The order is one at a denominator root and zero elsewhere. -/
def poleOrder (ν : ℂ) (ε : ℤ) : ℕ :=
  RealInducedSwapRegularizedFamily.order (choice ν ε)

/-- The symbol is scaled by the parameter to the pole order. The inverse power
of the slope makes the normalization independent of the speed along the line. -/
def symbol (ν : ℂ) (ε : ℤ) (b z : ℂ) (j : ℤ) : ℂ :=
  (b ^ poleOrder ν ε)⁻¹ * multiplier ν ε (choice ν ε) (b * z) j

theorem analyticAt_symbol (ν : ℂ) (ε : ℤ) (b : ℂ) (j : ℤ) :
    AnalyticAt ℂ (fun z => symbol ν ε b z j) 0 := by
  unfold symbol
  apply analyticAt_const.mul
  exact (RealInducedSwapRegularizedFamily.multiplier_analytic (validChoice ν ε) j).fun_comp_of_eq
    (analyticAt_const.mul analyticAt_id) (mul_zero b)

theorem symmetric_symbol (ν : ℂ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1) (b z : ℂ) :
    IsSymmetric ε ((-1) ^ ε.natAbs) (symbol ν ε b z) := by
  intro j hj
  unfold symbol
  rw [RealInducedSwapRegularizedFamily.multiplier_symmetric ν hε (choice ν ε) (b * z) j hj]
  ring

theorem symbol_eq_scaled_generic (ν : ℂ) (ε : ℤ) {b z : ℂ} (hb : b ≠ 0) (hz : z ≠ 0)
    {j : ℤ} (hj : Even (j - ε)) :
    symbol ν ε b z j = z ^ poleOrder ν ε * genericMultiplier (ν + b * z) ε j := by
  rw [symbol, RealInducedSwapRegularizedFamily.multiplier_eq_scaled_generic
    (validChoice ν ε) (mul_ne_zero hb hz) hj, mul_pow]
  change (b ^ poleOrder ν ε)⁻¹ * (b ^ poleOrder ν ε * z ^ poleOrder ν ε *
    genericMultiplier (ν + b * z) ε j) = _
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hb), one_mul]

/-- A neighborhood of `ν` meets the integer lattice only possibly at `ν`. -/
theorem eventually_isolated_integer (ν : ℂ) :
    ∀ᶠ w in 𝓝 ν, ∀ i : ℤ, w = (i : ℂ) → w = ν := by
  let integers := ((↑) : ℤ → ℂ) '' {i : ℤ | (i : ℂ) ≠ ν}
  have hclosed : IsClosed integers :=
    Complex.isClosedEmbedding_intCast.isClosedMap _ (isClosed_discrete _)
  have hν : ν ∈ integersᶜ := by
    rintro ⟨i, hi, h⟩
    exact hi h
  filter_upwards [hclosed.isOpen_compl.mem_nhds hν] with w hw i h
  by_contra hne
  exact hw ⟨i, by
    change (i : ℂ) ≠ ν
    rwa [← h], h.symm⟩

private theorem intCast_exceptional (ε : ℤ) (m : ℕ) :
    ((ε + 2 * (m : ℤ) + 1 : ℤ) : ℂ) = (ε : ℂ) + 2 * m + 1 := by
  push_cast
  rfl

theorem eventually_generic (ν : ℂ) (ε : ℤ) {b : ℂ} (hb : b ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → IsGenericParameter (ν + b * z) ε := by
  have ht : Tendsto (fun z : ℂ => ν + b * z) (𝓝 0) (𝓝 ν) := by
    have h : ContinuousAt (fun z : ℂ => ν + b * z) 0 :=
      continuousAt_const.add (continuousAt_const.mul continuousAt_id)
    change Tendsto (fun z : ℂ => ν + b * z) (𝓝 0) (𝓝 (ν + b * 0)) at h
    rwa [mul_zero, add_zero] at h
  filter_upwards [ht.eventually (eventually_isolated_integer ν)] with z hz hne
  have hν : ν + b * z ≠ ν := by simpa using mul_ne_zero hb hne
  constructor
  · intro m hm
    exact hν (hz (ε + 2 * (m : ℤ) + 1) (hm.trans (intCast_exceptional ε m).symm))
  · intro m hm
    exact hν (hz (-(ε + 2 * (m : ℤ) + 1)) (by rw [Int.cast_neg, intCast_exceptional, hm]))

theorem eventually_recurrent_symbol (ν : ℂ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    {b : ℂ} (hb : b ≠ 0) :
    ∀ᶠ z in 𝓝 0, IsRecurrent (ν + b * z + 1) ε (symbol ν ε b z) := by
  filter_upwards [eventually_generic ν ε hb] with z hz
  intro j hj
  by_cases he : z = 0
  · subst z
    have hr := RealInducedSwapRegularizedFamily.multiplier_recurrent hε (validChoice ν ε) j hj
    simp only [symbol, mul_zero, add_zero]
    linear_combination (b ^ poleOrder ν ε)⁻¹ * hr
  · have hj' : Even (j + 2 - ε) := by
      obtain ⟨q, hq⟩ := hj
      exact ⟨q + 1, by omega⟩
    rw [symbol_eq_scaled_generic ν ε hb he hj', symbol_eq_scaled_generic ν ε hb he hj]
    have hr := isRecurrent_genericMultiplier_of_ne hε (hz he).2 j hj
    linear_combination (z ^ poleOrder ν ε) * hr

theorem total_poleOrder_le_one (ν : ℂ) {ε : ℤ} (hε : 0 ≤ ε) :
    poleOrder ν ε + poleOrder (-ν) ε ≤ 1 := by
  have h₁ := validChoice ν ε
  have h₂ := validChoice (-ν) ε
  unfold poleOrder
  cases hq : choice ν ε with
  | none => cases choice (-ν) ε <;> simp [RealInducedSwapRegularizedFamily.order]
  | some l =>
    cases hq' : choice (-ν) ε with
    | none => simp [RealInducedSwapRegularizedFamily.order]
    | some r =>
      rw [hq] at h₁
      rw [hq'] at h₂
      change ν = -((ε : ℂ) + 2 * l + 1) at h₁
      change -ν = -((ε : ℂ) + 2 * r + 1) at h₂
      have he : (0 : ℝ) ≤ ε := by exact_mod_cast hε
      have h₁' := congrArg Complex.re h₁
      have h₂' := congrArg Complex.re h₂
      simp at h₁' h₂'
      linarith only [h₁', h₂', he, Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]

theorem eventually_symbol_mul_opposite (ν : ℂ) (ε : ℤ) {b : ℂ} (hb : b ≠ 0)
    {j : ℤ} (hj : Even (j - ε)) :
    (fun z => symbol (-ν) ε (-b) z j * symbol ν ε b z j) =ᶠ[𝓝 0]
      (fun z => z ^ (poleOrder ν ε + poleOrder (-ν) ε)) := by
  let f (z : ℂ) := symbol (-ν) ε (-b) z j * symbol ν ε b z j
  let g (z : ℂ) := z ^ (poleOrder ν ε + poleOrder (-ν) ε)
  have hoff : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → f z = g z := by
    filter_upwards [eventually_generic ν ε hb] with z hz hne
    dsimp only [f, g]
    rw [symbol_eq_scaled_generic _ _ (neg_ne_zero.mpr hb) hne hj,
      symbol_eq_scaled_generic _ _ hb hne hj,
      show -ν + -b * z = -(ν + b * z) by ring, pow_add]
    calc
      _ = (z ^ poleOrder ν ε * z ^ poleOrder (-ν) ε) *
          (genericMultiplier (ν + b * z) ε j * genericMultiplier (-(ν + b * z)) ε j) := by ring
      _ = _ := by rw [genericMultiplier_mul_neg (hz hne), mul_one]
  have hpunct : f =ᶠ[𝓝[≠] (0 : ℂ)] g := by
    filter_upwards [hoff.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with z hf hz
    exact hf hz
  have hf : ContinuousAt f 0 :=
    ((analyticAt_symbol (-ν) ε (-b) j).mul (analyticAt_symbol ν ε b j)).continuousAt
  have hg : ContinuousAt g 0 := continuous_id.continuousAt.pow _
  have hzero : f 0 = g 0 := tendsto_nhds_unique_of_eventuallyEq
    hf.continuousWithinAt.tendsto hg.continuousWithinAt.tendsto hpunct
  filter_upwards [hoff] with z hz
  by_cases he : z = 0
  · simpa only [he] using hzero
  · exact hz he

/-- A regularized affine crossing and the regularized opposite crossing are
analytic at zero and multiply to one power of the parameter at most. -/
def RealRegularizedCrossingSymbolsStatement : Prop :=
  ∀ (ν : ℂ) (ε : ℤ) (b : ℂ), (ε = 0 ∨ ε = 1) → b ≠ 0 →
    poleOrder ν ε + poleOrder (-ν) ε ≤ 1 ∧
    (∀ j, AnalyticAt ℂ (fun z => symbol ν ε b z j) 0) ∧
    (∀ z, IsSymmetric ε ((-1) ^ ε.natAbs) (symbol ν ε b z)) ∧
    (∀ᶠ z in 𝓝 0, IsRecurrent (ν + b * z + 1) ε (symbol ν ε b z)) ∧
    (∀ j, Even (j - ε) →
      (fun z => symbol (-ν) ε (-b) z j * symbol ν ε b z j) =ᶠ[𝓝 0]
        (fun z => z ^ (poleOrder ν ε + poleOrder (-ν) ε)))

theorem realRegularizedCrossingSymbols : RealRegularizedCrossingSymbolsStatement := by
  intro ν ε b hε hb
  exact ⟨total_poleOrder_le_one ν (by omega), analyticAt_symbol ν ε b, symmetric_symbol ν hε b,
    eventually_recurrent_symbol ν hε hb, fun _ => eventually_symbol_mul_opposite ν ε hb⟩

end Langlands.Archimedean.RealRegularizedCrossingSymbols
