import Langlands.HarmonicAnalysis.Bicharacter.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Inner products of finite sums of lattice characters -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Set

/-- Two finite sums of lattice characters with nonzero scalar coefficients have nonzero
inner product on `L` exactly when some two frequencies agree modulo its annihilator. -/
def LatticeCharacterInnerProductStatement {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y] {e : Y → Y → ℂ}
    (he : IsSelfDualBicharacter e) (μ : Measure Y) [μ.IsAddHaarMeasure]
    {I J : Type*} (L : AddSubgroup Y)
    (s : Finset I) (t : Finset J) (a : I → Y) (b : J → Y) (c d : ℂ) : Prop :=
  IsOpen (L : Set Y) → IsCompact (L : Set Y) → c ≠ 0 → d ≠ 0 →
  ((∫ x in (L : Set Y),
      (c * ∑ i ∈ s, e x (a i)) * starRingEnd ℂ (d * ∑ j ∈ t, e x (b j)) ∂μ) ≠ 0 ↔
    ∃ i ∈ s, ∃ j ∈ t, a i - b j ∈ he.annihilator (L : Set Y))

variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [MeasurableSpace Y] [BorelSpace Y] {e : Y → Y → ℂ} (he : IsSelfDualBicharacter e)
  (μ : Measure Y) [μ.IsAddHaarMeasure]

private theorem integral_bicharacter_subgroup (L : AddSubgroup Y) (hLo : IsOpen (L : Set Y))
    (z : Y) :
    (∫ x in (L : Set Y), e x z ∂μ) =
      (he.annihilator (L : Set Y) : Set Y).indicator (fun _ => (μ.real L : ℂ)) z := by
  rw [← BicharacterFourier.Internal.bicharacterFourier_indicator μ he L hLo,
    bicharacterFourier_apply, ← integral_indicator hLo.measurableSet]
  congr 1
  funext x
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx, indicator_of_mem hx, mul_one, he.symm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

theorem latticeCharacterInnerProduct {I J : Type*} (L : AddSubgroup Y)
    (s : Finset I) (t : Finset J) (a : I → Y) (b : J → Y) (c d : ℂ) :
    LatticeCharacterInnerProductStatement he μ L s t a b c d := by
  classical
  intro hLo hLc hc hd
  let A := he.annihilator (L : Set Y)
  let N (i : I) (j : J) : ℕ := if a i - b j ∈ A then 1 else 0
  have hConj (x y : Y) : starRingEnd ℂ (e x y) = e x (-y) := by
    rw [he.symm x y, he.conj_apply, he.symm (-y) x]
  have hExpand (x : Y) :
      (c * ∑ i ∈ s, e x (a i)) * starRingEnd ℂ (d * ∑ j ∈ t, e x (b j)) =
        (c * starRingEnd ℂ d) * ∑ i ∈ s, ∑ j ∈ t, e x (a i - b j) := by
    rw [map_mul, map_sum, mul_mul_mul_comm, Finset.sum_mul_sum]
    simp only [sub_eq_add_neg, he.map_add_right, hConj]
  have hcont (i : I) (j : J) : Continuous fun x => e x (a i - b j) :=
    he.continuous.comp (continuous_id.prodMk continuous_const)
  let : IsFiniteMeasure (μ.restrict (L : Set Y)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hLc.measure_lt_top⟩
  have hInt (i : I) (j : J) : Integrable (fun x => e x (a i - b j)) (μ.restrict (L : Set Y)) :=
    (integrable_const (1 : ℝ)).mono' (hcont i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (he.norm_eq_one x _).le)
  have hSumInt :
      (∫ x in (L : Set Y), ∑ i ∈ s, ∑ j ∈ t, e x (a i - b j) ∂μ) =
        ∑ i ∈ s, ∑ j ∈ t, ∫ x in (L : Set Y), e x (a i - b j) ∂μ := by
    rw [integral_finsetSum s (f := fun i x => ∑ j ∈ t, e x (a i - b j))
      (fun i _ => integrable_finsetSum t (fun j _ => hInt i j))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum t (fun j _ => hInt i j)
  have hCount (i : I) (j : J) : (∫ x in (L : Set Y), e x (a i - b j) ∂μ) =
      (μ.real L : ℂ) * (N i j : ℂ) := by
    rw [integral_bicharacter_subgroup he μ L hLo]
    by_cases h : a i - b j ∈ A
    · rw [indicator_of_mem h]
      simp only [N, ite_eq_left h, Nat.cast_one, mul_one]
    · rw [indicator_of_notMem h]
      simp only [N, ite_eq_right h, Nat.cast_zero, mul_zero]
  have hFormula :
      (∫ x in (L : Set Y),
        (c * ∑ i ∈ s, e x (a i)) * starRingEnd ℂ (d * ∑ j ∈ t, e x (b j)) ∂μ) =
        ((c * starRingEnd ℂ d) * (μ.real L : ℂ)) * (↑(∑ i ∈ s, ∑ j ∈ t, N i j) : ℂ) := by
    simp_rw [hExpand, integral_const_mul, hSumInt, hCount]
    simp only [mul_assoc, Nat.cast_sum, Finset.mul_sum]
  have hVol : 0 < μ.real (L : Set Y) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLc.measure_lt_top.ne
  have hD : starRingEnd ℂ d ≠ 0 := (map_ne_zero_iff _ (starRingEnd ℂ).injective).2 hd
  have hConst := mul_ne_zero (mul_ne_zero hc hD) (Complex.ofReal_ne_zero.mpr hVol.ne')
  rw [hFormula, mul_ne_zero_iff, and_iff_right hConst, Nat.cast_ne_zero]
  constructor
  · intro hs
    by_contra! h
    refine hs (Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_)
    exact ite_eq_right (h i hi j hj)
  · rintro ⟨i, hi, j, hj, h⟩
    have hterm : N i j = 1 := ite_eq_left h
    have hJ : N i j ≤ ∑ k ∈ t, N i k := Finset.single_le_sum (fun k _ => Nat.zero_le _) hj
    have hI : (∑ k ∈ t, N i k) ≤ ∑ l ∈ s, ∑ k ∈ t, N l k :=
      Finset.single_le_sum (f := fun l => ∑ k ∈ t, N l k) (fun _ _ => Nat.zero_le _) hi
    exact (Nat.one_le_iff_ne_zero.mp (hterm ▸ hJ.trans hI))

end Langlands.HarmonicAnalysis
