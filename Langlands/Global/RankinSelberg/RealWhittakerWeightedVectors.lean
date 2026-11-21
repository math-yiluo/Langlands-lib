import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Archimedean.HeightWeightedRightTranslation
import Langlands.Representation.Archimedean.SmoothHilbert
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Weighted smooth-vector realizations of moderate real coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open Filter Set Topology
open scoped Manifold ContDiff Matrix.Norms.Operator ZeroAtInfty NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerWeightedVectors

open RealLocalWhittaker

variable {r N : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "E" => (Langlands.GeneralLinear (r + 1) ℝ →C₀ ℂ)
local notation "𝓘G" => matrixModel ℝ (r + 1)
local notation "R" => HeightWeightedRightTranslation.representation (A := M) (N + 1)

private theorem height_pos (g : G) : 0 < Archimedean.unitHeight g := zero_lt_one.trans_le (Archimedean.one_le_unitHeight g)

private theorem norm_entry_le_opNorm (A : M) (i j : Fin (r + 1)) : ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  change (‖A i j‖₊ : ℝ) ≤ _
  apply NNReal.coe_le_coe.mpr
  exact (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))

/-- The real matrix height is bounded by a constant times the square of the unit height. -/
theorem realMatrixHeight_le_unitHeight_sq (g : G) :
    realMatrixHeight g ≤ (2 * ((r + 1 : ℕ) : ℝ) ^ 2) * Archimedean.unitHeight g ^ 2 := by
  unfold realMatrixHeight
  have hp (i j : Fin (r + 1)) : ‖g.val i j‖ ^ 2 + ‖(g⁻¹).val i j‖ ^ 2 ≤ 2 * Archimedean.unitHeight g ^ 2 := by
    have h₁ := pow_le_pow_left₀ (norm_nonneg _) ((norm_entry_le_opNorm g.val i j).trans
      (Archimedean.norm_val_le_unitHeight g)) 2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) ((norm_entry_le_opNorm (g⁻¹).val i j).trans
      (Archimedean.norm_inv_le_unitHeight g)) 2
    linarith
  calc
    _ ≤ ∑ _i : Fin (r + 1), ∑ _j : Fin (r + 1), 2 * Archimedean.unitHeight g ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- A smooth scalar function whose every right-derivative word satisfies the same unit-height
power bound, with a different constant allowed for each word. -/
def HasHeightDerivativeBound (r N : ℕ) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) : Prop :=
  ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W ∧
    ∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖iteratedRightDerivative r Xs W g‖ ≤ C * Archimedean.unitHeight g ^ N

/-- The same height exponent controls every derivative of a right derivative. -/
theorem hasHeightDerivativeBound_rightDerivative {W : G → ℂ}
    (hW : HasHeightDerivativeBound r N W) (X : M) :
    HasHeightDerivativeBound r N (rightDerivative 𝓘G X W) := by
  refine ⟨contMDiff_rightDerivative hW.1 X, fun Xs => ?_⟩
  simpa only [iteratedRightDerivative, List.foldr_append, List.foldr_cons, List.foldr_nil] using
    hW.2 (Xs ++ [X])

private def weight (N : ℕ) (x : G) : ℝ := (Archimedean.unitHeight x ^ (N + 1))⁻¹

private theorem weight_pos (N : ℕ) (x : G) : 0 < weight N x := inv_pos.mpr (pow_pos (height_pos x) _)

private theorem continuous_weight (N : ℕ) : Continuous (weight (r := r) N) :=
  (Archimedean.continuous_unitHeight.pow _).inv₀ (fun x => (pow_pos (height_pos x) _).ne')

private theorem tendsto_weighted_of_bound {W : G → ℂ} {C : ℝ}
    (hC : ∀ x, ‖W x‖ ≤ C * Archimedean.unitHeight x ^ N) :
    Tendsto (fun x => weight N x • W x) (cocompact G) (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  let B := max 1 (C / ε)
  have hB : IsCompact {x : G | Archimedean.unitHeight x ≤ B} := Archimedean.isCompact_unitHeight_sublevel (le_max_left _ _)
  filter_upwards [hB.compl_mem_cocompact] with x hx
  have hxB : B < Archimedean.unitHeight x := lt_of_not_ge hx
  have hH := height_pos x
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (weight_pos N x).le]
  calc
    _ ≤ weight N x * (C * Archimedean.unitHeight x ^ N) := mul_le_mul_of_nonneg_left (hC x) (weight_pos N x).le
    _ = C / Archimedean.unitHeight x := by
      unfold weight
      rw [pow_succ]
      field_simp [hH.ne', pow_ne_zero N hH.ne']
    _ < ε := by
      apply (div_lt_iff₀ hH).mpr
      have h := (le_max_right (1 : ℝ) (C / ε)).trans_lt hxB
      rw [div_lt_iff₀ hε, mul_comm] at h
      exact h

/-- A coefficient represented after division by one power more than its common exponent. -/
def weightedVector {W : G → ℂ} (hW : HasHeightDerivativeBound r N W) : E where
  toFun x := weight N x • W x
  continuous_toFun := (continuous_weight N).smul hW.1.continuous
  zero_at_infty' := by
    obtain ⟨C, _, hC⟩ := hW.2 []
    exact tendsto_weighted_of_bound hC

@[simp] theorem weightedVector_apply {W : G → ℂ} (hW : HasHeightDerivativeBound r N W) (x : G) :
    weightedVector hW x = (Archimedean.unitHeight x ^ (N + 1))⁻¹ • W x := rfl

private theorem representation_weighted_apply {W : G → ℂ} (hW : HasHeightDerivativeBound r N W)
    (g x : G) : R g (weightedVector hW) x = weight N x • W (x * g) := by
  rw [HeightWeightedRightTranslation.representation_apply, weightedVector_apply, ← mul_smul]
  congr 1
  unfold weight
  rw [div_pow]
  field_simp [pow_ne_zero (N + 1) (height_pos x).ne', pow_ne_zero (N + 1) (height_pos (x * g)).ne']

/-- Evaluation of a genuine right translate undoes the change of height weight. -/
theorem translate_weightedVector_apply {W : G → ℂ} (hW : HasHeightDerivativeBound r N W)
    (g x : G) : R g (weightedVector hW) x = (Archimedean.unitHeight x ^ (N + 1))⁻¹ • W (x * g) :=
  representation_weighted_apply hW g x

private def pointEval (x : G) : E →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => v x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun v => by
      change ‖v.toBCF x‖ ≤ 1 * ‖v.toBCF‖
      rw [one_mul]
      exact v.toBCF.norm_coe_le_norm x)

private theorem norm_pointEval_le (x : G) : ‖pointEval x‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by
      change ‖v.toBCF x‖ ≤ 1 * ‖v.toBCF‖
      rw [one_mul]
      exact v.toBCF.norm_coe_le_norm x)

private theorem hasFDerivAt_of_pointEval {f : M → E} {D : M → M →L[ℝ] E}
    {s : Set M} (hs : IsOpen s) {y : M} (hy : y ∈ s) (hD : ContinuousOn D s)
    (hf : ∀ z ∈ s, ∀ x : G, HasFDerivAt (fun w => f w x) ((pointEval x).comp (D z)) z) :
    HasFDerivAt f (D y) y := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsNear : ∀ᶠ z in 𝓝 y, z ∈ s := hs.mem_nhds hy
  have hSmall : ∀ᶠ L in 𝓝 (D y), ‖L - D y‖ < ε := eventually_norm_sub_lt (D y) hε
  have hNear : ∀ᶠ z in 𝓝 y, z ∈ s ∧ ‖D z - D y‖ < ε :=
    hsNear.and ((hD.continuousAt (hs.mem_nhds hy)).tendsto.eventually hSmall)
  obtain ⟨δ, hδ, hBall⟩ := Metric.eventually_nhds_iff_ball.mp hNear
  filter_upwards [Metric.ball_mem_nhds y hδ] with z hz
  change ‖(f z - f y - D y (z - y)).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  let L := pointEval x
  let v (q : M) := f q x - L (D y q)
  have hderiv (q : M) (hq : q ∈ Metric.ball y δ) :
      HasFDerivWithinAt v (L.comp (D q - D y)) (Metric.ball y δ) q := by
    have h := ((hf q (hBall q hq).1 x).sub (L.comp (D y)).hasFDerivAt).hasFDerivWithinAt
      (s := Metric.ball y δ)
    change HasFDerivWithinAt ((fun w => f w x) - ⇑((pointEval x).comp (D y)))
      ((pointEval x).comp (D q - D y)) (Metric.ball y δ) q
    rw [ContinuousLinearMap.comp_sub]
    exact h
  have hb (q : M) (hq : q ∈ Metric.ball y δ) : ‖L.comp (D q - D y)‖ ≤ ε :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_pointEval_le x) (hBall q hq).2.le (ContinuousLinearMap.opNorm_nonneg (D q - D y)) zero_le_one).trans_eq (one_mul _))
  have hm := (convex_ball y δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hb (Metric.mem_ball_self hδ) hz
  change ‖f z x - f y x - (D y (z - y)) x‖ ≤ _
  convert hm using 1
  congr 1
  change f z x - f y x - L (D y (z - y)) = v z - v y
  simp only [v, map_sub]
  abel

open Classical in
private def unitLift (A : M) : G := if h : IsUnit A then h.unit else 1

private theorem unitLift_val (g : G) : unitLift g.val = g := by
  simp [unitLift, g.isUnit]

private theorem unitLift_val_of_isUnit {A : M} (hA : IsUnit A) : (unitLift A).val = A := by
  simp [unitLift, hA]

private theorem contMDiffOn_unitLift : ContMDiffOn 𝓘(ℝ, M) 𝓘G ∞ (unitLift (r := r)) {A | IsUnit A} := by
  have hemb : IsOpenEmbedding (Units.val : G → M) := Units.isOpenEmbedding_val
  have h := contMDiffOn_isOpenEmbedding_symm (I := 𝓘G) (n := ∞) hemb
  rw [range_val_eq_setOf_isUnit] at h
  apply h.congr
  intro A hA
  obtain ⟨g, rfl⟩ := hA
  rw [unitLift_val, hemb.toOpenPartialHomeomorph_left_inv]

private theorem contDiffOn_inverseMatrix : ContDiffOn ℝ ∞
    (fun A : M => ((unitLift A)⁻¹).val) {A | IsUnit A} := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (Units.contMDiff_val.comp (contMDiff_inv 𝓘G ∞)).comp_contMDiffOn contMDiffOn_unitLift

private def coordinate (p : Fin (r + 1) × Fin (r + 1)) : M →L[ℝ] ℝ :=
  ({ toFun := fun A => A p.1 p.2
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : M →ₗ[ℝ] ℝ).toContinuousLinearMap

private def leftMultiplication : M →L[ℝ] M →L[ℝ] M :=
  ({ toFun := fun A => (mulLeftLinearMap (Fin (r + 1)) ℝ A).toContinuousLinearMap
     map_add' := fun A B => ContinuousLinearMap.ext fun X => Matrix.add_mul A B X
     map_smul' := fun c A => ContinuousLinearMap.ext fun X => Matrix.smul_mul c A X } :
    M →ₗ[ℝ] M →L[ℝ] M).toContinuousLinearMap

private theorem sum_coordinate_single (X : M) :
    (∑ p : Fin (r + 1) × Fin (r + 1), coordinate p X • Matrix.single p.1 p.2 (1 : ℝ)) = X := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_eq_single (i,j)]
  · simp [coordinate]
  · intro p _ hp
    have h : ¬(p.1 = i ∧ p.2 = j) := fun h => hp (Prod.ext h.1 h.2)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ h, smul_zero]
  · simp

private def orbitInCoordinates {W : G → ℂ} (hW : HasHeightDerivativeBound r N W) (A : M) : E :=
  R (unitLift A) (weightedVector hW)

private def orbitDerivative {W : G → ℂ} (hW : HasHeightDerivativeBound r N W) (A : M) : M →L[ℝ] E :=
  ∑ p : Fin (r + 1) × Fin (r + 1),
    ContinuousLinearMap.smulRightL ℝ M E
      ((coordinate p).comp (leftMultiplication (((unitLift A)⁻¹).val)))
      (orbitInCoordinates (hasHeightDerivativeBound_rightDerivative hW (Matrix.single p.1 p.2 1)) A)

private theorem orbitInCoordinates_eval_eqOn {W : G → ℂ}
    (hW : HasHeightDerivativeBound r N W) (x : G) :
    EqOn (fun A => orbitInCoordinates hW A x) (fun A => weight N x • unitsExtension W (x.val * A))
      {A : M | IsUnit A} := by
  intro A hA
  change R (unitLift A) (weightedVector hW) x = weight N x • unitsExtension W (x.val * A)
  rw [representation_weighted_apply,
    show x.val * A = (x * unitLift A).val by rw [Units.val_mul, unitLift_val_of_isUnit hA],
    unitsExtension_val]

private theorem hasFDerivAt_orbitInCoordinates_eval {W : G → ℂ}
    (hW : HasHeightDerivativeBound r N W) {A : M} (hA : IsUnit A) (x : G) :
    HasFDerivAt (fun B => orbitInCoordinates hW B x) ((pointEval x).comp (orbitDerivative hW A)) A := by
  let g := unitLift A
  have hg : g.val = A := unitLift_val_of_isUnit hA
  let L := fderiv ℝ (unitsExtension W) (x.val * A)
  have hxA : IsUnit (x.val * A) := x.isUnit.mul hA
  have hd : HasFDerivAt (fun B => unitsExtension W (x.val * B)) (L.comp (leftMultiplication x.val)) A :=
    (differentiableAt_unitsExtension hW.1 hxA).hasFDerivAt.comp A
      (leftMultiplication x.val).hasFDerivAt
  have hscale := hd.const_smul (weight N x)
  have hEq : (weight N x • (L.comp (leftMultiplication x.val))) =
      (pointEval x).comp (orbitDerivative hW A) := by
    apply ContinuousLinearMap.ext
    intro X
    let B := (g⁻¹).val * X
    have hTranslate (p : Fin (r + 1) × Fin (r + 1)) :
        pointEval x (R g (weightedVector (hasHeightDerivativeBound_rightDerivative hW
          (Matrix.single p.1 p.2 1)))) = weight N x • L ((x * g).val * Matrix.single p.1 p.2 1) := by
      change R g (weightedVector _) x = _
      rw [representation_weighted_apply, rightDerivative_eq_fderiv hW.1]
      simp only [L, Units.val_mul, hg]
    simp only [smul_apply, ContinuousLinearMap.comp_apply, orbitDerivative,
      sum_apply, map_sum]
    change weight N x • L (x.val * X) = ∑ p : Fin (r + 1) × Fin (r + 1),
      coordinate p B • pointEval x (R g (weightedVector (hasHeightDerivativeBound_rightDerivative hW
        (Matrix.single p.1 p.2 1))))
    simp only [hTranslate]
    calc
      _ = weight N x • L ((x * g).val * B) := by
        congr 2
        change x.val * X = (x * g).val * ((g⁻¹).val * X)
        rw [Units.val_mul, Matrix.mul_assoc x.val, ← Matrix.mul_assoc g.val, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Matrix.one_mul]
      _ = _ := by
        conv_lhs => rw [← sum_coordinate_single B, Matrix.mul_sum, map_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [Matrix.mul_smul, map_smul, smul_comm (weight N x) (coordinate p B)]
  rw [hEq] at hscale
  apply hscale.congr_of_eventuallyEq
  filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds hA] with B hB
  exact orbitInCoordinates_eval_eqOn hW x hB

set_option maxHeartbeats 600000 in
private theorem contDiffOn_orbitDerivative_nat (m : ℕ) {W : G → ℂ}
    (hW : HasHeightDerivativeBound r N W)
    (hOrb : ∀ {F : G → ℂ} (hF : HasHeightDerivativeBound r N F),
      ContDiffOn ℝ m (orbitInCoordinates hF) {A : M | IsUnit A}) :
    ContDiffOn ℝ m (orbitDerivative hW) {A : M | IsUnit A} := by
  unfold orbitDerivative
  apply ContDiffOn.sum
  intro p _
  let L := ContinuousLinearMap.compL ℝ M M ℝ (coordinate p)
  have hL : ContDiffOn ℝ m (fun A : M => L (leftMultiplication ((unitLift A)⁻¹).val))
      {A : M | IsUnit A} :=
    L.contDiff.comp_contDiffOn (leftMultiplication.contDiff.comp_contDiffOn
      (contDiffOn_inverseMatrix.of_le (by simp)))
  let Z := M →L[ℝ] E
  let : NormedAddCommGroup Z := inferInstanceAs (NormedAddCommGroup (M →L[ℝ] E))
  let : NormedSpace ℝ Z := inferInstanceAs (NormedSpace ℝ (M →L[ℝ] E))
  let Y := E →L[ℝ] Z
  let : NormedAddCommGroup Y := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] Z))
  let : NormedSpace ℝ Y := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] Z))
  let T : (M →L[ℝ] ℝ) →L[ℝ] Y := ContinuousLinearMap.smulRightL ℝ M E
  have hT : ContDiff ℝ (m : ℕ) T := T.contDiff
  have hFn : ContDiffOn ℝ (m : ℕ) (fun A : M => T (L (leftMultiplication ((unitLift A)⁻¹).val)))
      {A : M | IsUnit A} := hT.comp_contDiffOn hL
  exact hFn.clm_apply
    (hOrb (hasHeightDerivativeBound_rightDerivative hW (Matrix.single p.1 p.2 1)))

set_option maxHeartbeats 600000 in
private theorem contDiffOn_orbitInCoordinates_nat (m : ℕ) :
    ∀ {W : G → ℂ} (hW : HasHeightDerivativeBound r N W),
      ContDiffOn ℝ m (orbitInCoordinates hW) {A : M | IsUnit A} := by
  induction m with
  | zero =>
    intro W hW
    rw [Nat.cast_zero, contDiffOn_zero]
    have ht := HeightWeightedRightTranslation.continuous_orbit (A := M) (N + 1) (weightedVector hW)
    exact ht.comp_continuousOn contMDiffOn_unitLift.continuousOn
  | succ m ih =>
    intro W hW
    have hD := contDiffOn_orbitDerivative_nat m hW ih
    have hF (A : M) (hA : IsUnit A) : HasFDerivAt (orbitInCoordinates hW) (orbitDerivative hW A) A :=
      hasFDerivAt_of_pointEval isOpen_setOf_isUnit_matrix hA hD.continuousOn
        (fun _ hB x => hasFDerivAt_orbitInCoordinates_eval hW hB x)
    simp only [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      isOpen_setOf_isUnit_matrix.uniqueDiffOn).2
    exact ⟨by simp, orbitDerivative hW, hD, fun A hA => (hF A hA).hasFDerivWithinAt⟩

/-- The orbit map of a weighted moderate function is genuinely smooth in the Banach norm. -/
theorem weightedVector_isSmooth {W : G → ℂ} (hW : HasHeightDerivativeBound r N W) :
    Archimedean.IsSmoothVector 𝓘G R (weightedVector hW) := by
  have hf : ContDiffOn ℝ ∞ (orbitInCoordinates hW) {A : M | IsUnit A} :=
    contDiffOn_infty.2 fun m => contDiffOn_orbitInCoordinates_nat m hW
  have hm := (contMDiffOn_iff_contDiffOn.mpr hf).comp_contMDiff Units.contMDiff_val
    (fun g : G => Units.isUnit g)
  change ContMDiff 𝓘G 𝓘(ℝ, E) ∞ (fun g => R g (weightedVector hW))
  apply hm.congr
  intro g
  change R g (weightedVector hW) = R (unitLift g.val) (weightedVector hW)
  rw [unitLift_val]

private theorem lieDerivative_eq_orbitDerivative {W : G → ℂ}
    (hW : HasHeightDerivativeBound r N W) (X : M) :
    lieDerivative 𝓘G R X (weightedVector hW) = orbitDerivative hW (1 : M) X := by
  have h₁ : IsUnit (1 : M) := isUnit_one
  have hd := hasFDerivAt_of_pointEval isOpen_setOf_isUnit_matrix h₁
    (contDiffOn_orbitDerivative_nat 0 hW (contDiffOn_orbitInCoordinates_nat 0)).continuousOn
    (fun _ hA x => hasFDerivAt_orbitInCoordinates_eval hW hA x)
  have hcomp := mfderiv_comp (1 : G) hd.differentiableAt.mdifferentiableAt
    ((Units.contMDiff_val (n := ∞)).mdifferentiableAt (by simp))
  rw [mfderiv_units_val, ContinuousLinearMap.comp_id, mfderiv_eq_fderiv, Units.val_one, hd.fderiv] at hcomp
  have hfun : orbitMap R (weightedVector hW) = orbitInCoordinates hW ∘ (Units.val : G → M) := by
    funext g
    change R g (weightedVector hW) = R (unitLift g.val) (weightedVector hW)
    rw [unitLift_val]
  unfold lieDerivative
  rw [hfun, hcomp]
  rfl

/-- The Banach Lie derivative agrees with the scalar right derivative after weighting. -/
theorem lieDerivative_weightedVector {W : G → ℂ} (hW : HasHeightDerivativeBound r N W) (X : M) :
    lieDerivative 𝓘G R X (weightedVector hW) =
      weightedVector (hasHeightDerivativeBound_rightDerivative hW X) := by
  rw [lieDerivative_eq_orbitDerivative]
  ext x
  change ((pointEval x).comp (orbitDerivative hW (1 : M))) X = weight N x • rightDerivative 𝓘G X W x
  rw [rightDerivative_eq_fderiv_mul_left hW.1]
  let H (A : M) := unitsExtension W (x.val * A)
  have h := hasFDerivAt_orbitInCoordinates_eval hW (isUnit_one : IsUnit (1 : M)) x
  have hH : DifferentiableAt ℝ H 1 := differentiableAt_unitsExtension_mul_left hW.1 x
  have hh := hH.hasFDerivAt.const_smul (weight N x)
  have hSame : (fun A => orbitInCoordinates hW A x) =ᶠ[𝓝 (1 : M)] (weight N x • H) := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (isUnit_one : IsUnit (1 : M))] with A hA
    exact orbitInCoordinates_eval_eqOn hW x hA
  have hEq := h.unique (hh.congr_of_eventuallyEq hSame)
  exact congrArg (fun L : M →L[ℝ] ℂ => L X) hEq

/-- Smooth real coefficients with all right derivatives of one polynomial height order
are genuine Banach smooth vectors, and their Lie actions agree. -/
def RealWhittakerWeightedVectorsStatement : Prop :=
  ∀ (r N : ℕ) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (hW : HasHeightDerivativeBound r N W),
    let ρ := HeightWeightedRightTranslation.representation
      (A := Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (N + 1)
    Archimedean.IsSmoothVector (matrixModel ℝ (r + 1)) ρ (weightedVector hW) ∧
      ∀ X, lieDerivative (matrixModel ℝ (r + 1)) ρ X (weightedVector hW) =
        weightedVector (hasHeightDerivativeBound_rightDerivative hW X)

theorem realWhittakerWeightedVectors : RealWhittakerWeightedVectorsStatement := by
  intro r N W hW
  exact ⟨weightedVector_isSmooth hW, lieDerivative_weightedVector hW⟩

end Langlands.Global.RankinSelbergGlobal.RealWhittakerWeightedVectors
