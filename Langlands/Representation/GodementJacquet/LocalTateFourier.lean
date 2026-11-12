import Langlands.Representation.GodementJacquet.LocalTateLattice

/-! # Additive characters and Fourier integrals of lattice-coset indicators -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : Normalization F)

section Character

variable {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
include hψ

omit [IsNonarchimedeanLocalField F] in
theorem char_eq_one_of_mem_ball_zero {x : F} (hx : x ∈ N.ball 0) : ψ.complex x = 1 := by
  rw [UnitaryAdditiveCharacter.complex_apply, hψ.1 x (N.mem_ball_zero.mp hx)]
  rfl

omit [IsNonarchimedeanLocalField F] in
/-- Outside the dual lattice the character is nontrivial on the lattice. -/
theorem exists_char_ne_one {y : F} {n : ℤ} (hy : y ∉ N.ball (-n)) :
    ∃ t ∈ N.ball n, ψ.complex (t * y) ≠ 1 := by
  have hy' : (N.ϖ : F) ^ n * y ∉ (valuation F).integer := by
    rwa [← N.mem_ball_zero, ← N.mem_ball_neg_iff_mul]
  by_contra h
  push Not at h
  apply hy'
  apply hψ.2
  intro z hz
  have hmem : (N.ϖ : F) ^ n * z ∈ N.ball n := by
    simpa using N.mul_mem_ball (N.ϖ_zpow_mem_ball n) (N.mem_ball_zero.mpr hz)
  have h1 := h _ hmem
  rw [UnitaryAdditiveCharacter.complex_apply] at h1
  apply Circle.ext
  rw [show (N.ϖ : F) ^ n * y * z = (N.ϖ : F) ^ n * z * y by ring, h1]
  rfl

variable [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

open Classical in
/-- Additive orthogonality on the lattices `ϖ ^ n O`. -/
theorem integral_ball_char (n : ℤ) (y : F) :
    ∫ x in (N.ball n : Set F), ψ.complex (x * y) ∂ν =
      if y ∈ N.ball (-n) then ((ν (N.ball n)).toReal : ℂ) else 0 := by
  split_ifs with hy
  · have h1 : Set.EqOn (fun x => ψ.complex (x * y)) (fun _ => (1 : ℂ)) (N.ball n : Set F) := by
      intro x hx
      apply N.char_eq_one_of_mem_ball_zero hψ
      simpa using N.mul_mem_ball hx hy
    rw [setIntegral_congr_fun (N.measurableSet_ball n) h1, setIntegral_const]
    simp [Measure.real]
  · obtain ⟨t, ht, hne⟩ := N.exists_char_ne_one hψ hy
    set I := ∫ x in (N.ball n : Set F), ψ.complex (x * y) ∂ν with hI
    have hshift : I = ψ.complex (t * y) * I := by
      have key := integral_add_right_eq_self (μ := ν)
        ((N.ball n : Set F).indicator (fun x => ψ.complex (x * y))) t
      rw [hI, ← integral_indicator (N.measurableSet_ball n)]
      conv_lhs => rw [← key]
      rw [← integral_const_mul]
      congr 1
      funext x
      have hiff : x + t ∈ (N.ball n : Set F) ↔ x ∈ (N.ball n : Set F) := by
        simp only [SetLike.mem_coe]
        exact (N.ball n).add_mem_cancel_right ht
      by_cases hx : x ∈ (N.ball n : Set F)
      · rw [Set.indicator_of_mem (hiff.mpr hx), Set.indicator_of_mem hx, add_mul,
          AddChar.map_add_eq_mul, mul_comm]
      · rw [Set.indicator_of_notMem (fun h => hx (hiff.mp h)), Set.indicator_of_notMem hx,
          mul_zero]
    have h0 : (1 - ψ.complex (t * y)) * I = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h

open Classical in
/-- The plus-sign Fourier integral of the indicator of `x0 + ϖ ^ n O`. -/
theorem fourierIntegral_cosetIndicator (ν : AdditiveHaarMeasure F) (x0 : F) (n : ℤ) (y : F) :
    fourierIntegral ψ ν (N.cosetIndicator x0 n) y =
      ψ.complex (x0 * y) *
        (if y ∈ N.ball (-n) then ((ν.measure (N.ball n)).toReal : ℂ) else 0) := by
  have h1 := integral_add_right_eq_self (μ := ν.measure)
    (fun x => ψ.complex (x * y) * N.cosetIndicator x0 n x) x0
  rw [← N.integral_ball_char hψ ν.measure n y, ← integral_const_mul, fourierIntegral, ← h1,
    ← integral_indicator (N.measurableSet_ball n)]
  congr 1
  funext x
  rw [cosetIndicator_apply]
  by_cases hx : x ∈ N.ball n
  · rw [Set.indicator_of_mem (show x + x0 ∈ {x | x - x0 ∈ N.ball n} by simpa using hx),
      Set.indicator_of_mem (show x ∈ (N.ball n : Set F) from hx), mul_one, add_mul,
      AddChar.map_add_eq_mul, mul_comm]
  · rw [Set.indicator_of_notMem (show x + x0 ∉ {x | x - x0 ∈ N.ball n} by simpa using hx),
      Set.indicator_of_notMem (show x ∉ (N.ball n : Set F) from hx), mul_zero]

end Character

/-- Dilation `Φ ↦ Φ (b * ·)` of Schwartz--Bruhat functions by a unit. -/
def dilate (b : Fˣ) : SchwartzBruhat F →ₗ[ℂ] SchwartzBruhat F where
  toFun Φ := ⟨fun x => Φ ((b : F) * x),
    Φ.locallyConstant.comp_continuous (continuous_const.mul continuous_id),
    by simpa [smul_eq_mul] using Φ.hasCompactSupport.comp_smul b.ne_zero⟩
  map_add' Φ Ψ := rfl
  map_smul' c Φ := rfl

@[simp] theorem dilate_apply (b : Fˣ) (Φ : SchwartzBruhat F) (x : F) :
    dilate b Φ x = Φ ((b : F) * x) := rfl

variable [MeasurableSpace F] [BorelSpace F]

/-- Dilation and the plus-sign Fourier integral: the transform of `Φ (b * ·)`
is `|b|⁻¹ (FΦ) (b⁻¹ * ·)`. -/
theorem fourierIntegral_dilate (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (b : Fˣ) (Φ : SchwartzBruhat F) (y : F) :
    fourierIntegral ψ ν (dilate b Φ) y =
      ((N.abv (b : F))⁻¹ : ℂ) * fourierIntegral ψ ν Φ (((b⁻¹ : Fˣ) : F) * y) := by
  have hscale := HarmonicAnalysis.generalScalarHaarScalingStatement F N.q N.hq N.abv N.ϖ N.hϖ
    N.habvϖ N.habv1 ν.measure b
  have hemb : MeasurableEmbedding (fun x : F => (b : F) * x) :=
    (Homeomorph.mulLeft₀ (b : F) b.ne_zero).measurableEmbedding
  let g : F → ℂ := fun z => ψ.complex (z * (((b⁻¹ : Fˣ) : F) * y)) * Φ z
  have hg : ∀ x, g ((b : F) * x) = ψ.complex (x * y) * Φ ((b : F) * x) := by
    intro x
    simp only [g]
    congr 2
    rw [show (b : F) * x * (((b⁻¹ : Fˣ) : F) * y) = x * ((b : F) * ((b⁻¹ : Fˣ) : F)) * y by
      ring, Units.mul_inv, mul_one]
  rw [fourierIntegral, fourierIntegral]
  simp_rw [dilate_apply, ← hg]
  rw [← hemb.integral_map, hscale, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  simp [Shahidi.absUnits_apply]

end Normalization

end Langlands.GodementJacquet.LocalTate
