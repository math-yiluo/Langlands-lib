import Langlands.Global.RankinSelberg.RealRankRaisingSubgroup

/-! # Both Haar weights for the real rank-raising subgroup -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar)
open Langlands.RankinSelberg.GLDeterminantDensity (map_withDensity_comp map_withDensity_equiv)
open ArchimedeanLocal RealLastPivotChart

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace
private local instance (n : ℕ) : MeasurableSpace (lowerTriangularSubgroup n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (lowerTriangularSubgroup n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : LocallyCompactSpace (lowerTriangularSubgroup n ℝ) :=
  (lowerTriangularSubgroup_isClosed n).locallyCompactSpace
private local instance (r : ℕ) : MeasurableSpace (rankRaisingSubgroup r) := borel _
private local instance (r : ℕ) : BorelSpace (rankRaisingSubgroup r) := ⟨rfl⟩

local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "X" => fun r => Matrix (Fin 1) (Fin (r + 1)) ℝ
local notation "P" => fun r => X r × B
local notation "H" => rankRaisingSubgroup
local notation "chart" => rankRaisingHomeomorph
local notation "dx" => fun r ν => rectangularMeasure ν 1 (r + 1)

/-- The absolute determinant of the trailing block. -/
def trailingHeight (h : B) : ℝ≥0 := ‖h.val.val.det‖₊

private theorem trailingHeight_ne_zero (h : B) : trailingHeight h ≠ 0 :=
  nnnorm_ne_zero_iff.mpr (determinant h.val).ne_zero

private theorem continuous_trailingHeight : Continuous trailingHeight :=
  continuous_nnnorm.comp ((Units.continuous_val.comp
    (continuous_subtype_val : Continuous (fun h : B => h.val))).matrix_det)

private theorem trailingHeight_mul (h k : B) : trailingHeight (h * k) = trailingHeight h * trailingHeight k := by
  simp only [trailingHeight, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, nnnorm_mul]

private theorem trailingHeight_inv (h : B) : trailingHeight h⁻¹ = (trailingHeight h)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← trailingHeight_mul, inv_mul_cancel]
  simp [trailingHeight]

private theorem continuous_diagonal (r : ℕ) : Continuous (rankRaisingDiagonal r : B → _) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, rankRaisingDiagonal, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp only [hi, ite_true, Matrix.GeneralLinearGroup.val_det_apply]
    exact (Units.continuous_val.comp (continuous_subtype_val : Continuous (fun h : B => h.val))).matrix_det
  · simp only [hi, ite_false, Units.val_one, continuous_const]

private theorem det_diagonal (r : ℕ) (h : B) : (rankRaisingDiagonal r h).val.det = h.val.val.det := by
  rw [rankRaisingDiagonal, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.det_diagonal,
    Finset.prod_eq_single (0 : Fin (r + 1))]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

private theorem det_diagonal_inv (r : ℕ) (h : B) :
    (rankRaisingDiagonal r h)⁻¹.val.det = h.val.val.det⁻¹ := by
  change ((determinant (rankRaisingDiagonal r h)⁻¹ : ℝˣ) : ℝ) = _
  rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

/-- Left Haar density with respect to `dx d×h`. -/
def rankRaisingLeftDensity (r : ℕ) (h : B) : ℝ≥0 := (trailingHeight h ^ (r + 1))⁻¹

/-- The product measure with the rank-raising left Haar density, in the compensating subgroup. -/
def rankRaisingLeftHaar (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) : Measure (H r) :=
  ((dx r ν).prod (ρ.withDensity fun h => (rankRaisingLeftDensity r h : ℝ≥0∞))).map (chart r)

/-- The product measure with the rank-raising right Haar density, in the compensating subgroup. -/
def rankRaisingRightHaar (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) : Measure (H r) :=
  ((dx r ν).prod (ρ.withDensity fun h => (trailingHeight h : ℝ≥0∞))).map (chart r)

private theorem continuous_leftDensity (r : ℕ) : Continuous (rankRaisingLeftDensity r) :=
  (continuous_trailingHeight.pow _).inv₀ (fun h => pow_ne_zero _ (trailingHeight_ne_zero h))

private theorem map_rectangle {r : ℕ} (ν : AdditiveHaarMeasure ℝ)
    (A : Langlands.GeneralLinear 1 ℝ) (C : Langlands.GeneralLinear (r + 1) ℝ) :
    (dx r ν).map (fun x : X r => A.val * x * C.val) =
      (‖A.val.det‖₊ ^ (r + 1) * ‖C.val.det‖₊)⁻¹ • dx r ν := by
  let := ν.isAddHaar
  let := rectangularMeasure_isAddHaar ν 1 (r + 1)
  have hScale (a : ℝ) (ha : a ≠ 0) : ν.measure.map (fun x : ℝ => a * x) = (nnnormHom a)⁻¹ • ν.measure := by
    change ν.measure.map (fun x : ℝ => a • x) = _
    rw [map_addHaar_smul ν.measure ha, Module.finrank_self, pow_one, abs_inv,
      ← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
    rfl
  simpa only [Fintype.card_fin, pow_one, nnnormHom_apply] using
    haarMeasure_map_rectangular ν.measure nnnormHom hScale (dx r ν) A.val C.val A.det_ne_zero C.det_ne_zero

private theorem map_leftRow {r : ℕ} (ν : AdditiveHaarMeasure ℝ) (h : B) :
    (dx r ν).map (fun x : X r => h.val.val * x) = rankRaisingLeftDensity r h • dx r ν := by
  simpa only [Units.val_one, Matrix.mul_one, Matrix.det_one, nnnorm_one, mul_one,
    rankRaisingLeftDensity, trailingHeight] using map_rectangle (r := r) ν h.val 1

private theorem map_rightRow {r : ℕ} (ν : AdditiveHaarMeasure ℝ) (h : B) :
    (dx r ν).map (fun x : X r => x * (rankRaisingDiagonal r h)⁻¹.val) = trailingHeight h • dx r ν := by
  simpa only [Units.val_one, Matrix.one_mul, Matrix.det_one, nnnorm_one, one_pow, one_mul,
    det_diagonal_inv, nnnorm_inv, inv_inv, trailingHeight] using
    map_rectangle ν 1 (rankRaisingDiagonal r h)⁻¹

private theorem map_weighted (ρ : Measure B) (e : B ≃ᵐ B) (he : ρ.map e = ρ)
    (d : B → ℝ≥0) (hd : Continuous d) (c : ℝ≥0) (h : ∀ x, d (e.symm x) = c * d x) :
    (ρ.withDensity fun x => (d x : ℝ≥0∞)).map e = c • (ρ.withDensity fun x => (d x : ℝ≥0∞)) := by
  rw [map_withDensity_equiv, he]
  simp_rw [h, ENNReal.coe_mul]
  exact withDensity_smul (c : ℝ≥0∞) hd.measurable.coe_nnreal_ennreal

private theorem map_leftDensity (r : ℕ) (ρ : Measure B) [ρ.IsMulLeftInvariant] (h : B) :
    (ρ.withDensity fun k => (rankRaisingLeftDensity r k : ℝ≥0∞)).map (h * ·) =
      (trailingHeight h ^ (r + 1)) • (ρ.withDensity fun k => (rankRaisingLeftDensity r k : ℝ≥0∞)) := by
  let e := MeasurableEquiv.mulLeft h
  change (ρ.withDensity _).map e = _
  refine map_weighted ρ e (map_mul_left_eq_self ρ h) _ (continuous_leftDensity r) _ (fun k => ?_)
  change rankRaisingLeftDensity r (h⁻¹ * k) = _
  rw [rankRaisingLeftDensity, trailingHeight_mul, mul_pow, mul_inv, trailingHeight_inv, inv_pow, inv_inv]
  rfl

private theorem map_rightDensity (ρ : Measure B) [ρ.IsMulRightInvariant] (h : B) :
    (ρ.withDensity fun k => (trailingHeight k : ℝ≥0∞)).map (· * h) =
      (trailingHeight h)⁻¹ • (ρ.withDensity fun k => (trailingHeight k : ℝ≥0∞)) := by
  let e := MeasurableEquiv.mulRight h
  change (ρ.withDensity _).map e = _
  refine map_weighted ρ e (map_mul_right_eq_self ρ h) _ continuous_trailingHeight _ (fun k => ?_)
  change trailingHeight (k * h⁻¹) = _
  rw [trailingHeight_mul, trailingHeight_inv, mul_comm]

private theorem measurePreserving_shear {r : ℕ} (ν : AdditiveHaarMeasure ℝ)
    (ρ : Measure B) [SigmaFinite ρ] (f : B → X r) (hf : Continuous f) :
    MeasurePreserving (fun p : P r => (p.1 + f p.2, p.2)) ((dx r ν).prod ρ) ((dx r ν).prod ρ) := by
  let := rectangularMeasure_isAddHaar ν 1 (r + 1)
  have hF : Measurable (Function.uncurry fun (h : B) (x : X r) => x + f h) :=
    (continuous_snd.add (hf.comp continuous_fst)).measurable
  have hs := (MeasurePreserving.id ρ).skew_product hF (Filter.Eventually.of_forall fun h =>
    (measurePreserving_add_right (dx r ν) (f h)).map_eq)
  exact measurePreserving_swap.comp (hs.comp measurePreserving_swap)

private theorem isMulLeftInvariant_leftHaar {r : ℕ} (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B)
    [SigmaFinite ρ] [ρ.IsMulLeftInvariant] : (rankRaisingLeftHaar r ν ρ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨⟨x, h⟩, rfl⟩ := (chart r).surjective g
  let μ := ρ.withDensity fun k => (rankRaisingLeftDensity r k : ℝ≥0∞)
  let F (k : B) := (h.val⁻¹.val * x) * (rankRaisingDiagonal r k)⁻¹.val
  have hF : Continuous F := continuous_const.matrix_mul
    (Units.continuous_val.comp (continuous_diagonal r).inv)
  let D := Prod.map (fun y : X r => h.val.val * y) (fun k : B => h * k)
  let S (p : P r) := (p.1 + F p.2, p.2)
  have hS : MeasurePreserving S ((dx r ν).prod μ) ((dx r ν).prod μ) := measurePreserving_shear ν μ F hF
  have hD₁ : Measurable (fun y : X r => h.val.val * y) :=
    (continuous_const.matrix_mul continuous_id').measurable
  have hD₂ := measurable_const_mul h
  have hD : MeasurePreserving D ((dx r ν).prod μ) ((dx r ν).prod μ) := by
    refine ⟨hD₁.prodMap hD₂, ?_⟩
    rw [show D = Prod.map (fun y : X r => h.val.val * y) (h * ·) by rfl,
      ← map_prod_map _ _ hD₁ hD₂, map_leftRow, map_leftDensity, prod_smul_left, prod_smul_right,
      smul_smul, rankRaisingLeftDensity, inv_mul_cancel₀ (pow_ne_zero _ (trailingHeight_ne_zero h)), one_smul]
  have hDS := hD.comp hS
  have hAction : (fun q : H r => chart r (x, h) * q) ∘ chart r = chart r ∘ (D ∘ S) := by
    funext p
    apply Subtype.ext
    change rankRaisingSmoothingMatrix (x, h) * rankRaisingSmoothingMatrix p =
      rankRaisingSmoothingMatrix (D (S p))
    rw [rankRaisingSmoothingMatrix_mul]
    congr 1
    apply Prod.ext
    · change x * (rankRaisingDiagonal r p.2)⁻¹.val + h.val.val * p.1 =
        h.val.val * (p.1 + (h.val⁻¹.val * x) * (rankRaisingDiagonal r p.2)⁻¹.val)
      have he : h.val.val * h.val⁻¹.val = 1 := h.val.val_inv
      rw [Matrix.mul_add, ← Matrix.mul_assoc h.val.val (h.val⁻¹.val * x),
        ← Matrix.mul_assoc h.val.val h.val⁻¹.val, he, Matrix.one_mul]
      exact add_comm _ _
    · rfl
  change (((dx r ν).prod μ).map (chart r)).map (fun q => chart r (x, h) * q) = _
  rw [Measure.map_map (measurable_const_mul _) (chart r).continuous.measurable, hAction,
    ← Measure.map_map (chart r).continuous.measurable hDS.measurable, hDS.map_eq]
  rfl

private theorem isMulRightInvariant_rightHaar {r : ℕ} (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B)
    [SigmaFinite ρ] [ρ.IsMulRightInvariant] : (rankRaisingRightHaar r ν ρ).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨⟨x, h⟩, rfl⟩ := (chart r).surjective g
  let μ := ρ.withDensity fun k => (trailingHeight k : ℝ≥0∞)
  let F (k : B) := (k.val.val * x) * (rankRaisingDiagonal r h).val
  have hF : Continuous F := ((Units.continuous_val.comp
    (continuous_subtype_val : Continuous (fun k : B => k.val))).matrix_mul
      continuous_const).matrix_mul continuous_const
  let D := Prod.map (fun y : X r => y * (rankRaisingDiagonal r h)⁻¹.val) (fun k : B => k * h)
  let S (p : P r) := (p.1 + F p.2, p.2)
  have hS : MeasurePreserving S ((dx r ν).prod μ) ((dx r ν).prod μ) := measurePreserving_shear ν μ F hF
  have hD₁ : Measurable (fun y : X r => y * (rankRaisingDiagonal r h)⁻¹.val) :=
    (continuous_id'.matrix_mul continuous_const).measurable
  have hD₂ := measurable_mul_const h
  have hD : MeasurePreserving D ((dx r ν).prod μ) ((dx r ν).prod μ) := by
    refine ⟨hD₁.prodMap hD₂, ?_⟩
    rw [show D = Prod.map (fun y : X r => y * (rankRaisingDiagonal r h)⁻¹.val) (· * h) by rfl,
      ← map_prod_map _ _ hD₁ hD₂, map_rightRow, map_rightDensity, prod_smul_left, prod_smul_right,
      smul_smul, mul_inv_cancel₀ (trailingHeight_ne_zero h), one_smul]
  have hDS := hD.comp hS
  have hAction : (fun q : H r => q * chart r (x, h)) ∘ chart r = chart r ∘ (D ∘ S) := by
    funext p
    apply Subtype.ext
    change rankRaisingSmoothingMatrix p * rankRaisingSmoothingMatrix (x, h) =
      rankRaisingSmoothingMatrix (D (S p))
    rw [rankRaisingSmoothingMatrix_mul]
    congr 1
    apply Prod.ext
    · change p.1 * (rankRaisingDiagonal r h)⁻¹.val + p.2.val.val * x =
        (p.1 + (p.2.val.val * x) * (rankRaisingDiagonal r h).val) * (rankRaisingDiagonal r h)⁻¹.val
      have he : (rankRaisingDiagonal r h).val * (rankRaisingDiagonal r h)⁻¹.val = 1 :=
        (rankRaisingDiagonal r h).val_inv
      rw [Matrix.add_mul, Matrix.mul_assoc (p.2.val.val * x), he, Matrix.mul_one]
    · rfl
  change (((dx r ν).prod μ).map (chart r)).map (fun q => q * chart r (x, h)) = _
  rw [Measure.map_map (measurable_mul_const _) (chart r).continuous.measurable, hAction,
    ← Measure.map_map (chart r).continuous.measurable hDS.measurable, hDS.map_eq]
  rfl

private theorem weighted_isOpenPos (ρ : Measure B) [ρ.IsOpenPosMeasure] {d : B → ℝ≥0}
    (hd : Continuous d) (hpos : ∀ h, d h ≠ 0) :
    (ρ.withDensity fun h => (d h : ℝ≥0∞)).IsOpenPosMeasure := by
  refine ⟨fun U hU hne hz => hU.measure_ne_zero ρ hne ?_⟩
  exact withDensity_absolutelyContinuous' hd.measurable.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun h => ENNReal.coe_ne_zero.mpr (hpos h)) hz

/-- The density of left Haar measure with respect to right Haar measure on the
compensating subgroup. -/
def rankRaisingLeftRelativeDensity (r : ℕ) (g : H r) : ℝ≥0 :=
  rankRaisingLeftDensity (r + 1) ((chart r).symm g).2

/-- The two Haar weights differ by the inverse `(r + 2)`-nd power of the trailing
absolute determinant. -/
theorem withDensity_rightHaar_eq_leftHaar (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B)
    [SigmaFinite ρ] :
    (rankRaisingRightHaar r ν ρ).withDensity (fun g => (rankRaisingLeftRelativeDensity r g : ℝ≥0∞)) =
      rankRaisingLeftHaar r ν ρ := by
  let w := rankRaisingLeftDensity (r + 1)
  have hw : Measurable (fun h : B => (w h : ℝ≥0∞)) :=
    (continuous_leftDensity (r + 1)).measurable.coe_nnreal_ennreal
  have hh := continuous_trailingHeight.measurable.coe_nnreal_ennreal
  have hcomp (p : P r) : rankRaisingLeftRelativeDensity r (chart r p) = w p.2 := by
    rw [rankRaisingLeftRelativeDensity, (chart r).symm_apply_apply]
  unfold rankRaisingRightHaar rankRaisingLeftHaar
  rw [← map_withDensity_comp _ (chart r).measurableEmbedding]
  simp_rw [hcomp]
  rw [← prod_withDensity_right hw, ← withDensity_mul ρ hh hw]
  have he : (fun h : B => (trailingHeight h : ℝ≥0∞)) * (fun h : B => (w h : ℝ≥0∞)) =
      fun h : B => (rankRaisingLeftDensity r h : ℝ≥0∞) := by
    funext h
    simp only [Pi.mul_apply, ← ENNReal.coe_mul, w, rankRaisingLeftDensity]
    congr 1
    rw [pow_succ, mul_inv, ← mul_assoc, mul_right_comm (trailingHeight h),
      mul_inv_cancel₀ (trailingHeight_ne_zero h), one_mul]
  rw [he]

/-- The left density gives Haar measure and the right density gives right-invariant Haar data.
The supplied trailing measure is sigma finite and invariant on both sides. -/
def RealRankRaisingHaarStatement : Prop :=
  ∀ (r : ℕ) (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ]
    [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant],
    (rankRaisingLeftHaar r ν ρ).IsHaarMeasure ∧
    (rankRaisingRightHaar r ν ρ).IsMulRightInvariant ∧
    IsFiniteMeasureOnCompacts (rankRaisingRightHaar r ν ρ) ∧
    (rankRaisingRightHaar r ν ρ).IsOpenPosMeasure ∧
    (rankRaisingRightHaar r ν ρ).withDensity (fun g => (rankRaisingLeftRelativeDensity r g : ℝ≥0∞)) =
      rankRaisingLeftHaar r ν ρ

theorem realRankRaisingHaar : RealRankRaisingHaarStatement := by
  intro r ν ρ _ _ _
  let := rectangularMeasure_isAddHaar ν 1 (r + 1)
  have hData (d : B → ℝ≥0) (hd : Continuous d) (hpos : ∀ h, d h ≠ 0) :
      let μ := ((dx r ν).prod (ρ.withDensity fun h => (d h : ℝ≥0∞))).map (chart r)
      IsFiniteMeasureOnCompacts μ ∧ μ.IsOpenPosMeasure := by
    let μ := (dx r ν).prod (ρ.withDensity fun h => (d h : ℝ≥0∞))
    let := IsLocallyFiniteMeasure.withDensity_coe (μ := ρ) hd
    let := weighted_isOpenPos ρ hd hpos
    exact ⟨IsFiniteMeasureOnCompacts.map μ (chart r),
      (chart r).continuous.isOpenPosMeasure_map (chart r).surjective⟩
  obtain ⟨lf, lp⟩ := hData (rankRaisingLeftDensity r) (continuous_leftDensity r)
    (fun h => inv_ne_zero (pow_ne_zero _ (trailingHeight_ne_zero h)))
  obtain ⟨rf, rp⟩ := hData trailingHeight continuous_trailingHeight trailingHeight_ne_zero
  refine ⟨?_, isMulRightInvariant_rightHaar ν ρ, rf, rp, withDensity_rightHaar_eq_leftHaar r ν ρ⟩
  exact
    { toIsFiniteMeasureOnCompacts := lf
      toIsMulLeftInvariant := isMulLeftInvariant_leftHaar ν ρ
      toIsOpenPosMeasure := lp }

end Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral
