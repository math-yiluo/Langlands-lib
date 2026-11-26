import Langlands.Global.RankinSelberg.RealGapTriangularChart

/-! # The real triangular chart with retained determinant of absolute value one -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapUnitDeterminant

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (blockSum rankInclusion scalar scalarContinuous determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar det_rankInclusion)
open RealGapTriangularChart
open RealGapUpperTail (packedTail packedTail_conj firstRectangle laterRectangle)
open RealGapRightChart (map_withDensity_comp)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealIwasawa (torus torus_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance gapGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

variable (k q : ℕ)
local notation "Size" => k + q + 1
local notation "TailSize" => q + 1
local notation "Y" => Fin TailSize → ℝ
local notation "Compact" => unitaryCompact ℝ Size
local notation "Head" => Fin k → ℝ
local notation "Rectangle" => Matrix (Fin k) (Fin q) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent TailSize ℝ
local notation "Source" => Outer k q × (Rectangle × N)
local notation "Fiber" => (G k × (Compact × Head)) × (Rectangle × N)

local instance gapTailMeasurable : MeasurableSpace N := borel _
local instance gapTailBorel : BorelSpace N := ⟨rfl⟩

/-- The positive scalar that compensates the determinant of the tail diagonal in the leading block. -/
def normalizingScalar (y : Y) : ℝˣ :=
  Units.mk0 (Real.exp (-(∑ i, y i) / (k : ℝ))) (Real.exp_ne_zero _)

private theorem continuous_normalizingScalar : Continuous (normalizingScalar k q) := by
  apply (Units.isOpenEmbedding_val (R := ℝ)).isEmbedding.continuous_iff.mpr
  change Continuous (fun y : Y => Real.exp (-(∑ i, y i) / (k : ℝ)))
  exact Real.continuous_exp.comp (by fun_prop)

/-- The same scalar viewed as an element of the leading general linear group. -/
def leadingScalar (y : Y) : G k := scalar (normalizingScalar k q y)

private theorem continuous_leadingScalar : Continuous (leadingScalar k q) :=
  (scalarContinuous (R := ℝ) (n := k)).continuous.comp (continuous_normalizingScalar k q)

/-- The retained matrix after determinant normalization in the leading block. -/
def unitRetained (p : Outer k q) : G Size :=
  retainedMatrix k q p * rankInclusion TailSize (leadingScalar k q p.1.1.2)

/-- The retained matrix is continuous in the outer coordinates. -/
theorem continuous_unitRetained : Continuous (unitRetained k q) :=
  (continuous_retainedMatrix k q).mul ((Langlands.GeneralLinear.rankInclusionContinuous TailSize).continuous.comp
    ((continuous_leadingScalar k q).comp (by fun_prop)))

/-- The normalized chart uses the same later rectangle and upper unipotent coordinates. -/
def unitDeterminantChart (p : Source) : G Size :=
  unitRetained k q p.1 * (packedTail k q (laterRectangle k q p.2.1) p.2.2).val *
    rankInclusion TailSize p.1.1.1.1

private theorem norm_det_B (p : Outer k q) :
    (‖(retainedMatrix k q p).val.det‖₊ : ℝ) = Real.exp (∑ i, p.1.1.2 i) := by
  let y := p.1.1.2
  have hBlock : (blockSum ((1 : G k), torus y)).val.det = (torus y).val.det := by
    change (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (torus y).val)).det = _
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have hU : (packedTail k q (firstRectangle k q p.2) 1).val.val.det = 1 := by
    have h := (packedTail k q (firstRectangle k q p.2) 1).2
    rw [Matrix.det_of_isUpperTriangular h.1, Finset.prod_eq_one fun i _ => h.2 i]
  have hK : |p.1.2.val.val.det| = 1 :=
    Langlands.Archimedean.RealJacquetCoefficient.abs_det_eq_one_of_mem p.1.2.2
  unfold retainedMatrix
  rw [Units.val_mul, Matrix.det_mul, Units.val_mul, Matrix.det_mul, hU, mul_one, coe_nnnorm,
    Real.norm_eq_abs, abs_mul, hK, one_mul]
  change |(blockSum ((1 : G k), torus y)).val.det| = _
  rw [hBlock, torus_val, Matrix.det_diagonal, Finset.abs_prod]
  simp only [abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_sum]

private theorem norm_det_scalar (y : Y) :
    (‖(leadingScalar k q y).val.det‖₊ : ℝ) = Real.exp ((k : ℝ) * (-(∑ i, y i) / (k : ℝ))) := by
  have h : (leadingScalar k q y).val.det = (normalizingScalar k q y : ℝ) ^ k := by
    change (↑(Matrix.GeneralLinearGroup.det (scalar (normalizingScalar k q y) : G k)) : ℝ) = _
    rw [scalar, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val]
  rw [h, coe_nnnorm, norm_pow]
  change ‖Real.exp _‖ ^ k = _
  rw [Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_nat_mul]

/-- The normalized retained matrix has determinant of absolute value one. -/
theorem normalizedAbs_unitRetained (hk : 0 < k) (p : Outer k q) :
    ArchimedeanLocal.realNormalizedAbs (unitRetained k q p).val.det = 1 := by
  have h : (‖(unitRetained k q p).val.det‖₊ : ℝ) = 1 := by
    rw [unitRetained, Units.val_mul, Matrix.det_mul, nnnorm_mul, NNReal.coe_mul, det_rankInclusion,
      norm_det_B k q, norm_det_scalar k q, ← Real.exp_add]
    have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [show (∑ i, p.1.1.2 i) + (k : ℝ) * (-(∑ i, p.1.1.2 i) / (k : ℝ)) = 0 by
      field_simp; ring, Real.exp_zero]
  rw [coe_nnnorm, Real.norm_eq_abs] at h
  exact h

/-- The additive Jacobian from rescaling the later rectangle. -/
def normalizationWeight (y : Y) : ℝ≥0 := ‖(leadingScalar k q y).val.det‖₊ ^ q

/-- In logarithmic coordinates the new density is the inverse tail determinant to power `q`. -/
theorem normalizationWeight_eq (hk : 0 < k) (y : Y) :
    (normalizationWeight k q y : ℝ) = Real.exp (-(q : ℝ) * ∑ i, y i) := by
  rw [normalizationWeight, NNReal.coe_pow, norm_det_scalar k q, ← Real.exp_nat_mul]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  congr 1
  field_simp

/-- The normalization density is measurable in the logarithmic diagonal. -/
theorem measurable_normalizationWeight : Measurable (fun y : Y => (normalizationWeight k q y : ℝ≥0∞)) :=
  ((continuous_nnnorm.comp ((Units.continuous_val.comp (continuous_leadingScalar k q)).matrix_det)).pow
    q).measurable.coe_nnreal_ennreal

/-- The outer measure with the extra density of the normalized chart. -/
def unitOuterMeasure (μ : AdditiveHaarMeasure ℝ) (η₁ : Measure (G k)) (κ : Measure Compact) :
    Measure (Outer k q) :=
  (outerMeasure k q μ η₁ κ).withDensity (fun p => (normalizationWeight k q p.1.1.2 : ℝ≥0∞))

private def rescale (p : Source) : Source :=
  (((( (leadingScalar k q p.1.1.1.2)⁻¹ * p.1.1.1.1, p.1.1.1.2), p.1.1.2), p.1.2),
     ((↑((normalizingScalar k q p.1.1.1.2)⁻¹) : ℝ) • p.2.1, p.2.2))

private theorem rescale_chart (p : Source) : unitDeterminantChart k q (rescale k q p) = triangularRightChart k q p := by
  let u := normalizingScalar k q p.1.1.1.2
  let S := leadingScalar k q p.1.1.1.2
  let A := rankInclusion TailSize S
  let R := laterRectangle k q p.2.1
  have hScale : S⁻¹.val * R = laterRectangle k q ((↑u⁻¹ : ℝ) • p.2.1) := by
    have hS : S⁻¹.val = Matrix.diagonal (fun _ : Fin k => (u⁻¹ : ℝˣ).val) := by
      change (scalar u : G k)⁻¹.val = _
      rw [← map_inv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
      rfl
    ext i j
    rw [hS, Matrix.diagonal_mul]
    refine Fin.cases ?_ (fun j' => ?_) j <;> simp only [R, laterRectangle, Fin.cons_zero, Fin.cons_succ,
      mul_zero, Matrix.smul_apply, smul_eq_mul]
  have hConj := packedTail_conj k q S⁻¹ R p.2.2
  rw [hScale, map_inv, inv_inv] at hConj
  change retainedMatrix k q p.1 * A *
    (packedTail k q (laterRectangle k q ((↑u⁻¹ : ℝ) • p.2.1)) p.2.2).val *
    rankInclusion TailSize (S⁻¹ * p.1.1.1.1) =
    retainedMatrix k q p.1 * (packedTail k q R p.2.2).val * rankInclusion TailSize p.1.1.1.1
  rw [← hConj, map_mul, map_inv]
  change _ * A * (A⁻¹ * _ * A) * (A⁻¹ * _) = _
  group

private def shuffle : Source ≃ᵐ Y × Fiber :=
  let e₁ : Outer k q ≃ᵐ (G k × Y) × (Compact × Head) := MeasurableEquiv.prodAssoc
  let e₂ : ((G k × Y) × (Compact × Head)) ≃ᵐ (Y × G k) × (Compact × Head) :=
    MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)
  let e₃ : ((Y × G k) × (Compact × Head)) ≃ᵐ Y × (G k × (Compact × Head)) := MeasurableEquiv.prodAssoc
  ((e₁.trans (e₂.trans e₃)).prodCongr (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodAssoc

private theorem measurePreserving_shuffle (μ : AdditiveHaarMeasure ℝ) (ρ : Measure (G k)) [SFinite ρ]
    (κ : Measure Compact) [SFinite κ] (δ : Measure Y) [SFinite δ] :
    MeasurePreserving (shuffle k q)
      ((((ρ.prod δ).prod κ).prod (rowMeasure μ k)).prod
        ((rectangularMeasure μ k q).prod (entryHaar μ TailSize)))
      (δ.prod ((ρ.prod (κ.prod (rowMeasure μ k))).prod
        ((rectangularMeasure μ k q).prod (entryHaar μ TailSize)))) := by
  let η := entryHaar μ TailSize
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let ξ := rowMeasure μ k
  let ν := (rectangularMeasure μ k q).prod η
  have h₁ := measurePreserving_prodAssoc (ρ.prod δ) κ ξ
  have h₂ := (measurePreserving_swap (μ := ρ) (ν := δ)).prod (MeasurePreserving.id (κ.prod ξ))
  have h₃ := measurePreserving_prodAssoc δ ρ (κ.prod ξ)
  have h₄ := measurePreserving_prodAssoc δ (ρ.prod (κ.prod ξ)) ν
  exact h₄.comp ((h₃.comp (h₂.comp h₁)).prod (MeasurePreserving.id ν))

private def fiberRescale (y : Y) (p : Fiber) : Fiber :=
  (( (leadingScalar k q y)⁻¹ * p.1.1, p.1.2), ((↑((normalizingScalar k q y)⁻¹) : ℝ) • p.2.1, p.2.2))

private theorem measurable_rescaleFiber : Measurable (fun p : Y × Fiber => (p.1, fiberRescale k q p.1 p.2)) := by
  have hS : Measurable (fun y : Y => (leadingScalar k q y)⁻¹) := (continuous_leadingScalar k q).inv.measurable
  have hf : Measurable (fun p : Y × Fiber => (leadingScalar k q p.1)⁻¹ * p.2.1.1) :=
    (hS.comp measurable_fst).mul (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hu : Measurable (fun y : Y => (↑((normalizingScalar k q y)⁻¹) : ℝ)) :=
    (Units.continuous_val.comp (continuous_normalizingScalar k q).inv).measurable
  have hg : Measurable (fun p : Y × Fiber => (↑((normalizingScalar k q p.1)⁻¹) : ℝ) • p.2.2.1) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact (hu.comp measurable_fst).mul (Matrix.measurable_apply.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  exact measurable_fst.prodMk ((hf.prodMk (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
    (hg.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))

private theorem realVolume_map_mul (a : ℝ) (ha : a ≠ 0) :
    (volume : Measure ℝ).map (fun x : ℝ => a * x) = (nnnormHom a)⁻¹ • (volume : Measure ℝ) := by
  change (volume : Measure ℝ).map (fun x : ℝ => a • x) = _
  rw [Measure.map_addHaar_smul volume ha, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

private theorem map_fiberRescale (μ : AdditiveHaarMeasure ℝ) (ρ : Measure (G k)) [SFinite ρ]
    [ρ.IsMulLeftInvariant] (κ : Measure Compact) [SFinite κ] (y : Y) :
    let η := entryHaar μ TailSize
    let ν := ((ρ.prod (κ.prod (rowMeasure μ k))).prod
      ((rectangularMeasure μ k q).prod η))
    ν.map (fiberRescale k q y) = normalizationWeight k q y • ν := by
  intro η ν
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let ξ := κ.prod (rowMeasure μ k)
  let τ := rectangularMeasure μ k q
  let S := leadingScalar k q y
  let u := normalizingScalar k q y
  let f : G k → G k := fun g => S⁻¹ * g
  let g : Rectangle → Rectangle := fun R => (↑u⁻¹ : ℝ) • R
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have hg : Measurable g := ((continuous_const : Continuous (fun _ : Rectangle => (↑u⁻¹ : ℝ))).smul
    continuous_id).measurable
  have hS : S⁻¹.val = Matrix.diagonal (fun _ : Fin k => (u⁻¹ : ℝˣ).val) := by
    change (scalar u : G k)⁻¹.val = _
    rw [← map_inv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hScale (R : Rectangle) : S⁻¹.val * R * (1 : Matrix (Fin q) (Fin q) ℝ) = g R := by
    ext i j
    rw [Matrix.mul_one, hS, Matrix.diagonal_mul]
    rfl
  let : τ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  have hR := Langlands.HarmonicAnalysis.haarMeasure_map_rectangular (volume : Measure ℝ)
    (nnnormHom : ℝ →*₀ ℝ≥0) realVolume_map_mul τ S⁻¹.val (1 : Matrix (Fin q) (Fin q) ℝ)
    S⁻¹.det_ne_zero (by simp)
  have hd : ‖S⁻¹.val.det‖₊ = (‖S.val.det‖₊)⁻¹ := by
    have hh : (‖S⁻¹.val.det‖₊ : ℝ) * (‖S.val.det‖₊ : ℝ) = 1 := by
      rw [← NNReal.coe_mul, ← nnnorm_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, nnnorm_one,
        NNReal.coe_one]
    apply NNReal.eq
    rw [NNReal.coe_inv]
    exact eq_inv_of_mul_eq_one_left hh
  have hτ : τ.map g = normalizationWeight k q y • τ := by
    simpa only [hScale, Matrix.det_one, map_one, one_pow, mul_one, Fintype.card_fin, nnnormHom_apply,
      hd, inv_pow, inv_inv, normalizationWeight, S] using hR
  change ((ρ.prod ξ).prod (τ.prod η)).map (Prod.map (Prod.map f id) (Prod.map g id)) = _
  rw [← map_prod_map _ _ (hf.prodMap measurable_id) (hg.prodMap measurable_id),
    ← map_prod_map _ _ hf measurable_id, ← map_prod_map _ _ hg measurable_id,
    map_id, map_id, show ρ.map f = ρ from map_mul_left_eq_self ρ S⁻¹, hτ, prod_smul_left, prod_smul_right]

set_option synthInstance.maxHeartbeats 100000 in
private theorem measurePreserving_rescale (μ : AdditiveHaarMeasure ℝ) (η₁ : Measure (G k))
    [η₁.IsHaarMeasure] (κ : Measure Compact) [SFinite κ] :
    MeasurePreserving (rescale k q)
      ((outerMeasure k q μ η₁ κ).prod ((rectangularMeasure μ k q).prod (entryHaar μ TailSize)))
      ((unitOuterMeasure k q μ η₁ κ).prod ((rectangularMeasure μ k q).prod (entryHaar μ TailSize))) := by
  let δ := diagonalWeightMeasure k q
  let η := entryHaar μ TailSize
  let ξ := (rectangularMeasure μ k q).prod η
  let σ := outerMeasure k q μ η₁ κ
  let ν := ((η₁.prod (κ.prod (rowMeasure μ k))).prod ξ)
  let d (y : Y) : ℝ≥0∞ := normalizationWeight k q y
  have hd : Measurable d := measurable_normalizationWeight k q
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SFinite ν := by unfold ν ξ; infer_instance
  let ZMap := fun p : Y × Fiber => (p.1, fiberRescale k q p.1 p.2)
  have hm : Measurable ZMap := measurable_rescaleFiber k q
  have hMap : (δ.prod ν).map ZMap = (δ.withDensity d).prod ν := by
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    rw [lintegral_map hF hm]
    change (∫⁻ p, (F ∘ ZMap) p ∂δ.prod ν) = _
    rw [lintegral_prod _ (hF.comp hm).aemeasurable, lintegral_prod _ hF.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hd hF.lintegral_prod_right']
    apply lintegral_congr
    intro y
    have hm' : Measurable (fiberRescale k q y) := measurable_snd.comp (hm.comp (measurable_const.prodMk measurable_id))
    have hF' : Measurable (fun v : Fiber => F (y, v)) := hF.comp (measurable_const.prodMk measurable_id)
    change (∫⁻ v, F (y, fiberRescale k q y v) ∂ν) = d y * ∫⁻ v, F (y, v) ∂ν
    rw [← lintegral_map hF' hm', show ν.map (fiberRescale k q y) = _ from map_fiberRescale k q μ η₁ κ y]
    exact lintegral_smul_measure _ _
  let h₀ := measurePreserving_shuffle k q μ η₁ κ δ
  let h₁ := measurePreserving_shuffle k q μ η₁ κ (δ.withDensity d)
  have hDensity : (unitOuterMeasure k q μ η₁ κ).prod ξ =
      ((((η₁.prod (δ.withDensity d)).prod κ).prod (rowMeasure μ k)).prod ξ) := by
    unfold unitOuterMeasure outerMeasure
    symm
    rw [prod_withDensity_right hd]
    have hA := prod_withDensity_left (μ := η₁.prod δ) (ν := κ)
      (hd.comp measurable_snd)
    have hB := prod_withDensity_left (μ := (η₁.prod δ).prod κ) (ν := rowMeasure μ k)
      (hd.comp (measurable_snd.comp measurable_fst))
    exact congrArg (fun w => w.prod ξ) ((congrArg (fun w => w.prod (rowMeasure μ k)) hA).trans hB)
  have hRescale := (h₁.symm).comp ((show MeasurePreserving ZMap (δ.prod ν) ((δ.withDensity d).prod ν) from
    ⟨hm, hMap⟩).comp h₀)
  rw [← hDensity] at hRescale
  exact hRescale

/-- The normalized chart is continuous. -/
theorem continuous_unitDeterminantChart : Continuous (unitDeterminantChart k q) := by
  have hCont : Continuous (fun p : Source => rankInclusion TailSize (leadingScalar k q p.1.1.1.2)) :=
    (Langlands.GeneralLinear.rankInclusionContinuous TailSize).continuous.comp
      ((continuous_leadingScalar k q).comp (by fun_prop))
  have hPacked : Continuous (fun p : Source => (packedTail k q (laterRectangle k q p.2.1) p.2.2).val) := by
    have h := continuous_triangularRightChart k q
    let F (p : Source) : Source := ((((1, p.1.1.1.2), p.1.1.2), p.1.2), p.2)
    have hF : Continuous F := by unfold F; fun_prop
    have hh := ((continuous_retainedMatrix k q).comp continuous_fst).inv.mul (h.comp hF)
    have hEq : (fun p : Source => (retainedMatrix k q p.1)⁻¹ * triangularRightChart k q (F p)) =
        (fun p : Source => (packedTail k q (laterRectangle k q p.2.1) p.2.2).val) := by
      funext p
      have hR : retainedMatrix k q (F p).1 = retainedMatrix k q p.1 := rfl
      unfold triangularRightChart
      simp only [hR, F, map_one, mul_one, inv_mul_cancel_left]
    exact hEq ▸ hh
  exact ((((continuous_retainedMatrix k q).comp continuous_fst).mul hCont).mul hPacked).mul
    ((Langlands.GeneralLinear.rankInclusionContinuous TailSize).continuous.comp (by fun_prop))

/-- Haar integration in a triangular chart whose retained matrix has determinant of absolute value one. -/
def RealGapUnitDeterminantStatement : Prop :=
  ∀ (_hk : 0 < k) (μ : AdditiveHaarMeasure ℝ) (η : Measure (G Size)) (η₁ : Measure (G k))
    (κ : Measure Compact),
    η.IsHaarMeasure → η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    η = c • ((unitOuterMeasure k q μ η₁ κ).prod
      ((rectangularMeasure μ k q).prod (entryHaar μ TailSize))).map (unitDeterminantChart k q)

set_option maxHeartbeats 1200000 in
theorem realGapUnitDeterminant : RealGapUnitDeterminantStatement k q := by
  intro hk μ η η₁ κ hη hη₁ hκ hκinv
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N := (Langlands.GeneralLinear.upperEntryCoordinates (K := ℝ) TailSize).secondCountableTopology
  obtain ⟨c, hc, hHaar⟩ := realGapTriangularChart k q hk μ η η₁ κ hη hη₁ hκ hκinv
  have hRescale := measurePreserving_rescale k q μ η₁ κ
  have hCoord : unitDeterminantChart k q ∘ rescale k q = triangularRightChart k q := funext (rescale_chart k q)
  refine ⟨c, hc, ?_⟩
  rw [hHaar, ← hCoord, ← Measure.map_map (continuous_unitDeterminantChart k q).measurable
    hRescale.measurable, hRescale.map_eq]

end Langlands.Global.RankinSelbergGlobal.RealGapUnitDeterminant
