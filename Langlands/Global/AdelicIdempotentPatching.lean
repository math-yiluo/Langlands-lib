import Langlands.Global.NumberFieldAdeleTensorNorm
import Mathlib.Order.Filter.Finite

/-! # Idempotent refinements of finite covers of the adele ring -/

noncomputable section

open Filter NumberField IsDedekindDomain

namespace Langlands.Global

variable {K : Type*} [Field K] [NumberField K]

/-- A finite family generating the unit ideal in the full adele ring can be patched to a
unit by a partition of unity of orthogonal idempotents. At every place choose a nonzero
entry, preferring a local unit at finite places. The Bézout relation gives a local unit
among the entries at almost all finite places. -/
theorem exists_adele_idempotent_patch {ι : Type*} [Fintype ι] (d : ι → Adeles K)
    (hd : Ideal.span (Set.range d) = ⊤) :
    ∃ e : ι → Adeles K, (∑ i, e i) = 1 ∧ (∀ i, e i * e i = e i) ∧
      (∀ i j, i ≠ j → e i * e j = 0) ∧ IsUnit (∑ i, e i * d i) := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (Ideal.eq_top_iff_one _ |>.mp hd)
  have hi (v : InfinitePlace K) : ∑ i, (a i).1 v * (d i).1 v = 1 := by
    change ∑ i, adeleInfiniteEvaluation K v (a i) * adeleInfiniteEvaluation K v (d i) = 1
    simpa only [map_sum, map_mul, map_one] using congrArg (adeleInfiniteEvaluation K v) ha
  have hf (v : HeightOneSpectrum (𝓞 K)) : ∑ i, (a i).2 v * (d i).2 v = 1 := by
    change ∑ i, adeleFiniteEvaluation K v (a i) * adeleFiniteEvaluation K v (d i) = 1
    simpa only [map_sum, map_mul, map_one] using congrArg (adeleFiniteEvaluation K v) ha
  have hinf (v : InfinitePlace K) : ∃ i, (d i).1 v ≠ 0 := by
    by_contra! he
    simpa only [he, mul_zero, Finset.sum_const_zero, zero_ne_one] using hi v
  have hfin (v : HeightOneSpectrum (𝓞 K)) : ∃ i, (d i).2 v ≠ 0 := by
    by_contra! he
    simpa only [he, mul_zero, Finset.sum_const_zero, zero_ne_one] using hf v
  have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ∀ i, Valued.v ((a i).2 v) ≤ 1 ∧ Valued.v ((d i).2 v) ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [(a i).2.cofinite_mem_adicCompletionIntegers,
      (d i).2.cofinite_mem_adicCompletionIntegers] with v ha' hd'
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp ha',
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hd'⟩
  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ∃ i, Valued.v ((d i).2 v) = 1 := by
    filter_upwards [hint] with v hv
    by_contra! hh
    have hlt (i : ι) : Valued.v ((a i).2 v * (d i).2 v) < 1 := by
      rw [Valuation.map_mul]
      exact (mul_le_mul_of_nonneg_right (hv i).1 zero_le).trans_lt
        (by simpa using lt_of_le_of_ne (hv i).2 (hh i))
    have h := (Valued.v : Valuation (v.adicCompletion K) _).map_sum_lt one_ne_zero
      (fun i (_ : i ∈ Finset.univ) => hlt i)
    rw [hf v, Valuation.map_one] at h
    exact (lt_irrefl _ h)
  have hfChoose (v : HeightOneSpectrum (𝓞 K)) : ∃ i, (d i).2 v ≠ 0 ∧
      ((∃ j, Valued.v ((d j).2 v) = 1) → Valued.v ((d i).2 v) = 1) := by
    by_cases huv : ∃ j, Valued.v ((d j).2 v) = 1
    · obtain ⟨i, hi'⟩ := huv
      refine ⟨i, ?_, fun _ => hi'⟩
      intro h
      rw [h, Valuation.map_zero] at hi'
      exact zero_ne_one hi'
    · obtain ⟨i, hi'⟩ := hfin v
      exact ⟨i, hi', fun h => (huv h).elim⟩
  choose ti hti using hinf
  choose tf htf htf' using hfChoose
  let e (i : ι) : Adeles K :=
    ((fun v => if i = ti v then 1 else 0),
      RestrictedProduct.mk (fun v => if i = tf v then 1 else 0) (Eventually.of_forall fun v => by
        split <;> simp))
  have hei (i : ι) (v : InfinitePlace K) :
      adeleInfiniteEvaluation K v (e i) = if i = ti v then 1 else 0 := rfl
  have hef (i : ι) (v : HeightOneSpectrum (𝓞 K)) :
      adeleFiniteEvaluation K v (e i) = if i = tf v then 1 else 0 := rfl
  have hext {x y : Adeles K} (hi' : ∀ v, adeleInfiniteEvaluation K v x =
      adeleInfiniteEvaluation K v y) (hf' : ∀ v, adeleFiniteEvaluation K v x =
      adeleFiniteEvaluation K v y) : x = y :=
    Prod.ext (funext hi') (FiniteAdeleRing.ext K hf')
  have hsum (b : ι → Adeles K) :
      (∀ v, (∑ i, e i * b i : Adeles K).1 v = (b (ti v)).1 v) ∧
      (∀ v, (∑ i, e i * b i : Adeles K).2 v = (b (tf v)).2 v) := by
    constructor
    · intro v
      change adeleInfiniteEvaluation K v (∑ i, e i * b i) = adeleInfiniteEvaluation K v (b (ti v))
      simp only [map_sum, map_mul, hei, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    · intro v
      change adeleFiniteEvaluation K v (∑ i, e i * b i) = adeleFiniteEvaluation K v (b (tf v))
      simp only [map_sum, map_mul, hef, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · have h := hsum fun _ => 1
    simp only [mul_one] at h
    exact hext h.1 h.2
  · intro i
    apply hext <;> intro v
    · simp only [map_mul, hei]
      split <;> simp
    · simp only [map_mul, hef]
      split <;> simp
  · intro i j hij
    apply hext <;> intro v
    · simp only [map_mul, map_zero, hei]
      by_cases h : i = ti v
      · have hj : j ≠ ti v := fun h' => hij (h.trans h'.symm)
        simp [h, hj]
      · simp [h]
    · simp only [map_mul, map_zero, hef]
      by_cases h : i = tf v
      · have hj : j ≠ tf v := fun h' => hij (h.trans h'.symm)
        simp [h, hj]
      · simp [h]
  · rw [AdeleRing.isUnit_iff]
    refine ⟨fun v => (hsum d).1 v ▸ hti v, fun v => (hsum d).2 v ▸ htf v, ?_⟩
    filter_upwards [hgood] with v hv
    rw [(hsum d).2 v]
    exact htf' v hv

end Langlands.Global
