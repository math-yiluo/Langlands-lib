import Langlands.Global.RankinSelberg.ComplexLocalWhittakerSquareOperator

/-! # Matrix derivatives of left-translated complex coefficients -/

noncomputable section

open Filter
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "R" => rightDerivative (matrixModel ℂ n)

/-- Differentiation in matrix coordinates along the vector field `h ↦ h X`. -/
def matrixDirectionalDerivative (X : M) (f : M → ℂ) (h : M) : ℂ :=
  fderiv ℝ f h (h * X)

/-- The second derivative along the same vector field has its Hessian term and
the first derivative in the direction `h X²`. -/
theorem matrixDirectionalDerivative_twice (X : M) {f : M → ℂ} {h : M}
    (hf : ContDiffAt ℝ ∞ f h) :
    matrixDirectionalDerivative X (matrixDirectionalDerivative X f) h =
      (fderiv ℝ (fderiv ℝ f) h (h * X)) (h * X) + fderiv ℝ f h (h * X * X) := by
  let P : M →L[ℝ] M := (ContinuousLinearMap.mul ℝ M).flip X
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) h :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  change fderiv ℝ (fun y => fderiv ℝ f y (P y)) h (h * X) = _
  rw [fderiv_clm_apply hfd P.differentiableAt, P.fderiv]
  change fderiv ℝ f h (h * X * X) + (fderiv ℝ (fderiv ℝ f) h (h * X)) (h * X) = _
  exact add_comm _ _

private theorem rightDerivative_leftTranslate (X : M) (W : G → ℂ) (g h : G) :
    R X (fun k => W (g * k)) h = R X W (g * h) := by
  unfold rightDerivative
  have he : (fun k : G => W (g * (h * k))) = fun k : G => W (g * h * k) := by
    funext k
    rw [mul_assoc]
  rw [he]
  rfl

/-- The right derivative becomes `h ↦ h X` in the fixed matrix chart of
the left translate of a coefficient. -/
theorem matrixDirectionalDerivative_unitsExtension (X : M) {W : G → ℂ}
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W) (g h : G) :
    matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k))) h.val =
      R X W (g * h) := by
  have hV : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (fun k => W (g * k)) :=
    hW.comp contMDiff_mul_left
  rw [← rightDerivative_leftTranslate X W g h, rightDerivative_eq_fderiv hV]
  rfl

/-- Two right derivatives are computed by two matrix derivatives on that
fixed chart. -/
theorem matrixDirectionalDerivative_twice_unitsExtension (X : M) {W : G → ℂ}
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W)
    (hRW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (R X W)) (g h : G) :
    matrixDirectionalDerivative X
        (matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k)))) h.val =
      R X (R X W) (g * h) := by
  have he : matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k))) =ᶠ[𝓝 h.val]
      unitsExtension (fun k => R X W (g * k)) := by
    have hmem := isOpen_setOf_isUnit_matrix.mem_nhds h.isUnit
    filter_upwards [hmem] with y hy
    change IsUnit y at hy
    let k : G := hy.unit
    change matrixDirectionalDerivative X (unitsExtension (fun u => W (g * u))) k.val =
      unitsExtension (fun u => R X W (g * u)) k.val
    rw [matrixDirectionalDerivative_unitsExtension X hW, unitsExtension_val]
  change fderiv ℝ (matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k)))) h.val
      (h.val * X) = _
  rw [he.fderiv_eq]
  exact matrixDirectionalDerivative_unitsExtension X hRW g h

/-- The Hessian sum in the real coordinate fields on the open matrix chart. -/
def complexCoordinateHessianSum (f : M → ℂ) (h : M) : ℂ :=
  ∑ i : Bool × Fin n × Fin n,
    fderiv ℝ (fderiv ℝ f) h (h * matrixRealBasis n i) (h * matrixRealBasis n i)

private theorem matrixDirectionalDerivative_pair (f : M → ℂ) (h : M)
    (hf : ContDiffAt ℝ ∞ f h) (i j : Fin n) :
    let X : M := Matrix.single i j 1
    let Y : M := Matrix.single i j Complex.I
    matrixDirectionalDerivative X (matrixDirectionalDerivative X f) h +
        matrixDirectionalDerivative Y (matrixDirectionalDerivative Y f) h =
      fderiv ℝ (fderiv ℝ f) h (h * X) (h * X) +
        fderiv ℝ (fderiv ℝ f) h (h * Y) (h * Y) := by
  intro X Y
  have hY : Y = Complex.I • X := by simp [X, Y, Matrix.smul_single]
  have hcancel : h * Y * Y = -(h * X * X) := by
    simp only [hY, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Complex.I_mul_I, neg_one_smul]
  rw [matrixDirectionalDerivative_twice X hf, matrixDirectionalDerivative_twice Y hf, hcancel,
    map_neg]
  abel

/-- Pulling the coordinate square operator to the fixed matrix chart of a left
translate gives the Hessian sum. The first-order terms of a real direction
and its imaginary multiple cancel. -/
theorem complexCoordinateHessianSum_intertwiner {r : ℕ}
    {ds : List ComplexCharacterData} {a : ℂˣ}
    {B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B)
    (f : Automorphic.complexStandardKFinite (r + 1) ds)
    (g h : Langlands.GeneralLinear (r + 1) ℂ) :
    complexCoordinateHessianSum (unitsExtension (fun k => B f (g * k))) h.val =
      B (coordinateSquareOperator ds f) (g * h) := by
  let u := unitsExtension (fun k => B f (g * k))
  have hu : ContDiffAt ℝ ∞ u h.val :=
    ((contDiffOn_unitsExtension ((hB.2.1 f).comp contMDiff_mul_left)) h.val h.isUnit).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds h.isUnit)
  have hsm (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
      ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞
        (rightDerivative (matrixModel ℂ (r + 1)) X (B f)) := by
    let v := envelopingAction (complexStandardLie (r + 1) ds) (realGenerator (r + 1) X) f
    rw [← hB.2.2.2.2 X f v (realGenerator_action ds X f)]
    exact hB.2.1 v
  rw [complexCoordinateSquareDifferential_intertwiner hB f]
  simp only [complexCoordinateHessianSum, Fintype.sum_prod_type, matrixRealBasis_apply]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  unfold complexCoordinateSquareDifferential
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← matrixDirectionalDerivative_twice_unitsExtension _ (hB.2.1 f) (hsm _) g h,
    ← matrixDirectionalDerivative_twice_unitsExtension _ (hB.2.1 f) (hsm _) g h,
    matrixDirectionalDerivative_pair u h.val hu i j]
  exact add_comm _ _

/-- The real principal symbol of the Hessian sum is positive on every
nonzero real covector at each invertible matrix. -/
theorem complexCoordinateHessianSymbol_pos (h : G) (ξ : M →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    0 < ∑ i : Bool × Fin n × Fin n, (ξ (h.val * matrixRealBasis n i)) ^ 2 := by
  have hnonneg : 0 ≤ ∑ i : Bool × Fin n × Fin n, (ξ (h.val * matrixRealBasis n i)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine lt_of_le_of_ne hnonneg fun he => ?_
  have hz (i : Bool × Fin n × Fin n) : ξ (h.val * matrixRealBasis n i) = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ (h.val *
      matrixRealBasis n i)))).mp he.symm i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  have hmul (m : M) : ξ (h.val * m) = 0 := by
    calc
      _ = ξ (h.val * ∑ i, (matrixRealBasis n).repr m i • matrixRealBasis n i) :=
        congrArg (fun y : M => ξ (h.val * y)) ((matrixRealBasis n).sum_repr m).symm
      _ = _ := by
        simp only [Matrix.mul_sum, Matrix.mul_smul, map_sum, map_smul, hz, smul_zero,
          Finset.sum_const_zero]
  apply hξ
  ext m
  simpa only [← Matrix.mul_assoc, h.val_inv, Matrix.one_mul, zero_apply] using
    hmul (h.inv * m)

end Langlands.Global.RankinSelbergGlobal
