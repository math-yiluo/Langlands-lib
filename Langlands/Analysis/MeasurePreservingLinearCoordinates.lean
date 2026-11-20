import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Lebesgue-measure-preserving linear coordinate changes

A linear map `ℝⁿ → ℝ^{n'}` that preserves Lebesgue measure forces `n = n'`, is bijective and
has determinant `±1`; composing an integrand with a linear map of determinant `±1` does not change
its Lebesgue integral; and the coordinates `j ↦ Φ (L eⱼ)` of a linear form `Φ` along the images
of the standard basis under `L` are obtained from the coordinates `i ↦ Φ eᵢ` by the transpose of
the matrix of `L`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis

open MeasureTheory
open scoped Pointwise

/-- A linear map `ℝⁿ → ℝ^{n'}` preserving Lebesgue measure forces `n = n'`: the preimage of
`2 • B` is `2 • τ⁻¹(B)`, whose measures scale by `2^{n'}` and `2ⁿ`. -/
theorem eq_of_measurePreserving_linearMap {n n' : ℕ} (τ : (Fin n → ℝ) →ₗ[ℝ] (Fin n' → ℝ))
    (hτ : MeasurePreserving τ volume volume) : n = n' := by
  set B : Set (Fin n' → ℝ) := Metric.ball 0 1 with hB
  have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hpre : (τ : (Fin n → ℝ) → Fin n' → ℝ) ⁻¹' ((2 : ℝ) • B) = (2 : ℝ) • (τ ⁻¹' B) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
      · rw [map_smul, ← hxy, smul_smul]
        norm_num
        exact hy
      · rw [smul_smul]
        norm_num
    · rintro ⟨y, hy, rfl⟩
      exact ⟨τ y, hy, (map_smul τ 2 y).symm⟩
  have h2B : MeasurableSet ((2 : ℝ) • B) := (Metric.isOpen_ball.smul₀ two_ne_zero).measurableSet
  have h1 := hτ.measure_preimage h2B.nullMeasurableSet
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have h2 := hτ.measure_preimage hBm.nullMeasurableSet
  rw [hpre, Measure.addHaar_smul, Measure.addHaar_smul, h2, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h1
  have h3 : ENNReal.ofReal |(2 : ℝ) ^ n| = ENNReal.ofReal |(2 : ℝ) ^ n'| :=
    (ENNReal.mul_left_inj hB0 hBtop).1 h1
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)] at h3
  have h4 : (2 : ℝ) ^ n = 2 ^ n' :=
    (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 h3
  exact Nat.pow_right_injective le_rfl (by exact_mod_cast h4)

/-- A linear map `ℝⁿ → ℝ^{n'}` preserving Lebesgue measure is surjective: a proper subspace is
Lebesgue-null, while the preimage of the range is everything. -/
theorem surjective_of_measurePreserving_linearMap {n n' : ℕ}
    (τ : (Fin n → ℝ) →ₗ[ℝ] (Fin n' → ℝ)) (hτ : MeasurePreserving τ volume volume) :
    Function.Surjective τ := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin n' → ℝ)) _ hne
  have hmeas : MeasurableSet (LinearMap.range τ : Set (Fin n' → ℝ)) :=
    (Submodule.closed_of_finiteDimensional _).measurableSet
  have h1 := hτ.measure_preimage hmeas.nullMeasurableSet
  have huniv : (τ : (Fin n → ℝ) → Fin n' → ℝ) ⁻¹' (LinearMap.range τ) = Set.univ :=
    Set.eq_univ_of_forall fun x => LinearMap.mem_range_self τ x
  rw [huniv, h0] at h1
  have hpos := Metric.measure_ball_pos (volume : Measure (Fin n → ℝ)) (0 : Fin n → ℝ) one_pos
  exact (hpos.trans_le (measure_mono (Set.subset_univ _))).ne' h1

/-- A linear map `ℝⁿ → ℝⁿ` preserving Lebesgue measure has determinant `±1`. -/
theorem abs_det_eq_one_of_measurePreserving {n : ℕ} (τ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hτ : MeasurePreserving τ volume volume) : |LinearMap.det τ| = 1 := by
  have hsurj := surjective_of_measurePreserving_linearMap τ hτ
  have hinj : Function.Injective τ := LinearMap.injective_iff_surjective.2 hsurj
  have hdet : LinearMap.det τ ≠ 0 := by
    have hcoe : ((LinearEquiv.ofBijective τ ⟨hinj, hsurj⟩ : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = τ := LinearMap.ext fun _ => rfl
    have := (LinearEquiv.ofBijective τ ⟨hinj, hsurj⟩).isUnit_det'
    rw [hcoe] at this
    exact this.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℝ)) hdet
  rw [hτ.map_eq] at hmap
  set B : Set (Fin n → ℝ) := Metric.ball 0 1
  have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have h := congrArg (fun μ : Measure (Fin n → ℝ) => μ B) hmap
  simp only [Measure.smul_apply, smul_eq_mul] at h
  have h' : ENNReal.ofReal |(LinearMap.det τ)⁻¹| = 1 :=
    ((ENNReal.mul_left_inj hB0 hBtop).1 (h.symm.trans (one_mul _).symm))
  rw [ENNReal.ofReal_eq_one, abs_inv, inv_eq_one] at h'
  exact h'

/-- Composing with a linear map `ℝⁿ → ℝⁿ` of determinant `±1` preserves Lebesgue integrals. -/
theorem integral_comp_linearMap_of_abs_det_eq_one {n : ℕ} (ρ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hρ : |LinearMap.det ρ| = 1) {f : (Fin n → ℝ) → ℝ} (hf : AEStronglyMeasurable f volume) :
    ∫ y, f (ρ y) = ∫ y, f y := by
  have hdet : LinearMap.det ρ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hρ
    exact zero_ne_one hρ
  have hmap : Measure.map ρ volume = volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, abs_inv, hρ, inv_one,
      ENNReal.ofReal_one, one_smul]
  have hρc : Continuous ρ := LinearMap.continuous_of_finiteDimensional ρ
  rw [← integral_map hρc.aemeasurable (by rwa [hmap]), hmap]

/-- The coordinates `j ↦ Φ (L eⱼ)` of a linear form `Φ` along the images under `L` of the
standard basis are the transpose of the matrix of `L` applied to the coordinates `i ↦ Φ eᵢ`. -/
theorem linearForm_comp_single_eq_transpose {n : ℕ} (Φ : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (fun j => Φ (L (Pi.single j 1))) =
      Matrix.toLin' (LinearMap.toMatrix' L).transpose (fun i => Φ (Pi.single i 1)) := by
  ext j
  have hx : L (Pi.single j 1) = ∑ i, L (Pi.single j 1) i • (Pi.single i 1 : Fin n → ℝ) := by
    ext k
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [Matrix.mulVec, dotProduct, map_smul, smul_eq_mul]

/-- The transpose of the matrix of `L` has the determinant of `L`. -/
theorem det_toLin'_transpose_toMatrix' {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    LinearMap.det (Matrix.toLin' (LinearMap.toMatrix' L).transpose) = LinearMap.det L := by
  rw [LinearMap.det_toLin', Matrix.det_transpose, LinearMap.det_toMatrix']

end Langlands.Analysis
