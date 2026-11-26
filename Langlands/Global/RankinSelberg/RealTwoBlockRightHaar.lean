import Langlands.Global.RankinSelberg.RealTwoBlockHaar
import Langlands.Group.GL.SingletonBlocks
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Real two-block Haar integration with the first block on the right -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar

open Langlands.ProductLeviChamber (twoBlock)
open Langlands.Archimedean (unitaryCompact)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure haarMeasure_map_rectangular)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "Rect" => fun n k => Matrix (Fin k) (Fin (n - k)) ℝ
local notation "P" => fun n k => ((G k × G (n - k)) × Rect n k) × K n

local instance twoBlockRightGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance twoBlockRightGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance twoBlockRightGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance twoBlockRightGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

variable {n k : ℕ} (hk : 0 < k) (hkn : k < n)

local notation "B" => twoBlock n k hk hkn
local notation "U" => Langlands.GeneralLinear.BlockShape.unipotentRadical (twoBlock n k hk hkn) ℝ

theorem diagonalBlocks_mul (g₁ h₁ : G k) (g₂ h₂ : G (n - k)) :
    diagonalBlocks hk hkn (g₁ * h₁) (g₂ * h₂) =
      diagonalBlocks hk hkn g₁ g₂ * diagonalBlocks hk hkn h₁ h₂ := by
  change (B).leviEmbedding ℝ ((leviBlocks hk hkn).symm ((g₁, g₂) * (h₁, h₂))) = _
  rw [map_mul, map_mul]
  rfl

theorem diagonalBlocks_split (g₁ : G k) (g₂ : G (n - k)) :
    diagonalBlocks hk hkn g₁ g₂ = diagonalBlocks hk hkn 1 g₂ * diagonalBlocks hk hkn g₁ 1 := by
  simpa only [one_mul, mul_one] using diagonalBlocks_mul hk hkn 1 g₁ g₂ 1

/-- Block conjugation acts on the upper rectangle by left and inverse right multiplication. -/
theorem diagonalBlocks_conj_upperRectangle (g₁ : G k) (g₂ : G (n - k)) (X : Rect n k) :
    diagonalBlocks hk hkn g₁ g₂ * upperRectangle hk hkn X * (diagonalBlocks hk hkn g₁ g₂)⁻¹ =
      upperRectangle hk hkn (g₁.val * X * g₂⁻¹.val) := by
  let m := (leviBlocks hk hkn).symm (g₁, g₂)
  let e := rectangleCoordinates hk hkn
  let u := e.symm X
  let ij : (B).UpperPair := ⟨((0 : Fin 2), (1 : Fin 2)), by
    change (0 : ℕ) < 1
    decide⟩
  have h : (B).leviAction ℝ m u = e.symm (g₁.val * X * g₂⁻¹.val) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change (B).radicalCoordinates ℝ ((B).leviAction ℝ m u) ij = _
    rw [(B).radicalCoordinates_leviAction]
    exact congrArg (fun Z : Rect n k => g₁.val * Z * g₂⁻¹.val) (e.apply_symm_apply X)
  change ((B).leviEmbedding ℝ m * u.val.val * ((B).leviEmbedding ℝ m)⁻¹) = _
  rw [← (B).leviAction_apply_val ℝ m u, h]
  rfl

/-- The chart factor remaining after separating the right embedded first block. -/
def rightTail (g₂ : G (n - k)) (Y : Rect n k) (q : K n) : G n :=
  q.val * diagonalBlocks hk hkn 1 g₂ * upperRectangle hk hkn Y

theorem orthogonal_upper_diagonal_eq_rightTail (g₁ : G k) (g₂ : G (n - k))
    (X : Rect n k) (q : K n) :
    q.val * upperRectangle hk hkn X * diagonalBlocks hk hkn g₁ g₂ =
      rightTail hk hkn g₂ (X * g₂.val) q * diagonalBlocks hk hkn g₁ 1 := by
  have h := diagonalBlocks_conj_upperRectangle hk hkn 1 g₂ (X * g₂.val)
  rw [Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
    show g₂.val * g₂⁻¹.val = 1 from g₂.val_inv, Matrix.mul_one] at h
  have hcomm := congrArg (· * diagonalBlocks hk hkn 1 g₂) h
  rw [inv_mul_cancel_right] at hcomm
  unfold rightTail
  rw [diagonalBlocks_split hk hkn g₁ g₂]
  simp only [mul_assoc, hcomm]

/-- The determinant weight for moving the second diagonal block to the left of the rectangle. -/
def rightTailWeight (g₂ : G (n - k)) : ℝ≥0 := (‖g₂.val.det‖₊ ^ k)⁻¹

private theorem measurable_rightTailWeight :
    Measurable (fun g₂ : G (n - k) => (rightTailWeight (k := k) g₂ : ℝ≥0∞)) := by
  unfold rightTailWeight
  exact ((continuous_nnnorm.comp Units.continuous_val.matrix_det).pow k).measurable.inv.coe_nnreal_ennreal

private theorem realHaar_map_mul (ν : AdditiveHaarMeasure ℝ) (a : ℝ) (ha : a ≠ 0) :
    ν.measure.map (fun x : ℝ => a * x) = (‖a‖₊)⁻¹ • ν.measure := by
  change ν.measure.map (fun x : ℝ => a • x) = _
  rw [Measure.map_addHaar_smul ν.measure ha, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

private theorem rectangularMeasure_map_right (ν : AdditiveHaarMeasure ℝ) (g₂ : G (n - k)) :
    (rectangularMeasure ν k (n - k)).map (fun X => X * g₂.val) =
      rightTailWeight (k := k) g₂ • rectangularMeasure ν k (n - k) := by
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let ρ := rectangularMeasure ν k (n - k)
  let : ρ.IsAddHaarMeasure := rectangularMeasure_isAddHaar ν k (n - k)
  simpa only [Matrix.one_mul, Matrix.det_one, map_one, one_pow, one_mul, Fintype.card_fin,
    rightTailWeight, nnnormHom_apply]
    using haarMeasure_map_rectangular ν.measure (nnnormHom : ℝ →*₀ ℝ≥0)
      (realHaar_map_mul ν) ρ
      (1 : Matrix (Fin k) (Fin k) ℝ) g₂.val (by simp) g₂.det_ne_zero

private def rightShear (p : P n k) : P n k :=
  ((p.1.1, p.1.2 * p.1.1.2.val), p.2)

private theorem measurable_rightShear : Measurable (rightShear (n := n) (k := k)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk
    ((continuous_snd.matrix_mul (Units.continuous_val.comp (continuous_snd.comp continuous_fst))).measurable.comp
      measurable_fst)).prodMk measurable_snd

theorem continuous_diagonalBlocks :
    Continuous (fun p : G k × G (n - k) => diagonalBlocks hk hkn p.1 p.2) := by
  unfold diagonalBlocks
  exact ((B).leviEmbeddingContinuous ℝ).continuous.comp (leviBlocks hk hkn).symm.continuous

theorem continuous_upperRectangle : Continuous (upperRectangle hk hkn) := by
  unfold upperRectangle
  exact continuous_subtype_val.comp
    (continuous_subtype_val.comp (rectangleCoordinates hk hkn).symm.continuous)

theorem continuous_rightChart : Continuous (fun p : P n k =>
    rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1) := by
  have hlevi : Continuous (fun p : P n k => p.1.1) := continuous_fst.comp continuous_fst
  have hX : Continuous (fun p : P n k => p.1.2) := continuous_snd.comp continuous_fst
  have hq : Continuous (fun p : P n k => p.2.val) := continuous_subtype_val.comp continuous_snd
  have h1 : Continuous (fun p : P n k => diagonalBlocks hk hkn p.1.1.1 1) := by
    change Continuous ((fun z : G k × G (n - k) => diagonalBlocks hk hkn z.1 z.2) ∘
      fun p : P n k => (p.1.1.1, (1 : G (n - k))))
    exact (continuous_diagonalBlocks hk hkn).comp ((continuous_fst.comp hlevi).prodMk continuous_const)
  have h2 : Continuous (fun p : P n k => diagonalBlocks hk hkn 1 p.1.1.2) := by
    change Continuous ((fun z : G k × G (n - k) => diagonalBlocks hk hkn z.1 z.2) ∘
      fun p : P n k => ((1 : G k), p.1.1.2))
    exact (continuous_diagonalBlocks hk hkn).comp (continuous_const.prodMk (continuous_snd.comp hlevi))
  unfold rightTail
  exact ((hq.mul h2).mul ((continuous_upperRectangle hk hkn).comp hX)).mul h1

theorem measurable_rightChart : Measurable (fun p : P n k =>
    rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1) := by
  let : SecondCountableTopology (K n) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact (continuous_rightChart hk hkn).measurable

private theorem map_rightShear (ν : AdditiveHaarMeasure ℝ) (μ₁ : Measure (G k))
    (μ₂ : Measure (G (n - k))) [SFinite μ₁] [SFinite μ₂] (κ : Measure (K n)) [SFinite κ] :
    let ρ := ((μ₁.prod μ₂).prod (rectangularMeasure ν k (n - k))).prod κ
    ρ.map rightShear = ρ.withDensity (fun p => (rightTailWeight (k := k) p.1.1.2 : ℝ≥0∞)) := by
  let μL := μ₁.prod μ₂
  let μU := rectangularMeasure ν k (n - k)
  let ρ := (μL.prod μU).prod κ
  let : μU.IsAddHaarMeasure := rectangularMeasure_isAddHaar ν k (n - k)
  let D : P n k → ℝ≥0∞ := fun p => rightTailWeight (k := k) p.1.1.2
  have hD : Measurable D := measurable_rightTailWeight.comp
    (measurable_snd.comp (measurable_fst.comp measurable_fst))
  change ρ.map rightShear = ρ.withDensity D
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_rightShear, lintegral_withDensity_eq_lintegral_mul ρ hD hf]
  change (∫⁻ p, (f ∘ rightShear) p ∂(μL.prod μU).prod κ) =
    ∫⁻ p, (D * f) p ∂(μL.prod μU).prod κ
  rw [lintegral_prod _ (hf.comp measurable_rightShear).aemeasurable,
    lintegral_prod _ (hD.mul hf).aemeasurable]
  rw [lintegral_prod _ (hf.comp measurable_rightShear).lintegral_prod_right'.aemeasurable,
    lintegral_prod _ (hD.mul hf).lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro g
  let F : Rect n k → ℝ≥0∞ := fun Y => ∫⁻ q, f ((g, Y), q) ∂κ
  have hF : Measurable F := (hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).lintegral_prod_right'
  have hm : Measurable (fun X : Rect n k => X * g.2.val) := (continuous_id.matrix_mul continuous_const).measurable
  change (∫⁻ X, F (X * g.2.val) ∂μU) =
    ∫⁻ Y, ∫⁻ q, (rightTailWeight (k := k) g.2 : ℝ≥0∞) * f ((g, Y), q) ∂κ ∂μU
  rw [← lintegral_map hF hm, show μU.map (fun X => X * g.2.val) =
    rightTailWeight (k := k) g.2 • μU from rectangularMeasure_map_right ν g.2,
    lintegral_smul_measure, ENNReal.smul_def]
  simp_rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  rfl

/-- Real Haar measure with the first diagonal block on the right. The tail density is the
reciprocal of the `k`-th power of the absolute determinant of the second block. -/
def RealTwoBlockRightHaarStatement : Prop :=
  ∀ (n k : ℕ) (hk : 0 < k) (hkn : k < n) (ν : AdditiveHaarMeasure ℝ) (μ : Measure (G n))
    (μ₁ : Measure (G k)) (μ₂ : Measure (G (n - k))) (κ : Measure (K n)),
    μ.IsHaarMeasure → μ₁.IsHaarMeasure → μ₂.IsHaarMeasure →
    κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    let ρ := ((μ₁.prod μ₂).prod (rectangularMeasure ν k (n - k))).prod κ
    μ = c • Measure.map
      (fun p : P n k => rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1)
      (ρ.withDensity (fun p => (rightTailWeight (k := k) p.1.1.2 : ℝ≥0∞)))

theorem realTwoBlockRightHaar : RealTwoBlockRightHaarStatement := by
  intro n k hk hkn ν μ μ₁ μ₂ κ hμ hμ₁ hμ₂ hκ hκinv
  let : κ.IsHaarMeasure := hκ
  let : μ₁.IsHaarMeasure := hμ₁
  let : μ₂.IsHaarMeasure := hμ₂
  obtain ⟨c, hc, he⟩ := realTwoBlockHaar n k hk hkn ν μ μ₁ μ₂ κ hμ hμ₁ hμ₂ hκ hκinv
  refine ⟨c, hc, ?_⟩
  dsimp only
  rw [← map_rightShear (k := k) ν μ₁ μ₂ κ,
    Measure.map_map (measurable_rightChart hk hkn) measurable_rightShear, he]
  congr 2
  exact funext fun p => orthogonal_upper_diagonal_eq_rightTail hk hkn p.1.1.1 p.1.1.2 p.1.2 p.2

end Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar
