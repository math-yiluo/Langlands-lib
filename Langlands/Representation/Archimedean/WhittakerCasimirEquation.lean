import Langlands.Representation.Archimedean.WhittakerRootCovariance
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-! # The distribution equation from the trace Casimir and upper covariance -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Langlands.HarmonicAnalysis Langlands.GeneralLinear
open scoped Distributions Matrix.Norms.Operator

namespace Langlands.Archimedean

universe uF

variable {F : Type uF} [RCLike F] {r : ℕ}

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) F
local notation "D" => 𝓓(matrixUnitsOpen F (r + 1), ℂ)

/-- The diagonal terms of the Casimir after the positive-root reordering,
including the first-order diagonal commutators. -/
def matrixTraceDiagonalTestOperator (F : Type uF) [RCLike F] (n : ℕ) :
    𝓓(matrixUnitsOpen F n, ℂ) →L[ℂ] 𝓓(matrixUnitsOpen F n, ℂ) :=
  (∑ i : Fin n, ∑ k : Bool, (matrixLeftTestDerivative (matrixTraceUnit F n (i, i, k))).comp
    (matrixLeftTestDerivative (matrixTraceDualUnit F n (i, i, k)))) +
  ∑ p : MatrixPositiveRoot n, ∑ k : Bool,
    let b := matrixTraceUnit F n (p.val.1, p.val.2, k)
    let d := matrixTraceDualUnit F n (p.val.1, p.val.2, k)
    matrixLeftTestDerivative (b * d - d * b)

theorem matrixTraceUnit_mul_sub_dualUnit_isDiag (i j : Fin (r + 1)) (k : Bool) :
    let b := matrixTraceUnit F (r + 1) (i, j, k)
    let d := matrixTraceDualUnit F (r + 1) (i, j, k)
    (b * d - d * b).IsDiag := by
  intro b d a c hac
  change ((Matrix.single i j (if k then RCLike.I else 1 : F) *
      Matrix.single j i (if k then -RCLike.I else 1 : F)) -
    (Matrix.single j i (if k then -RCLike.I else 1 : F) *
      Matrix.single i j (if k then RCLike.I else 1 : F))) a c = 0
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  by_cases hi : i = a <;> by_cases hj : j = a <;>
    simp [Matrix.single, hi, hj, hac]

/-- The simple negative-root direction determined by the two
real frequencies of the additive character. -/
def matrixWhittakerLowerDirection (F : Type uF) [RCLike F] (r : ℕ) (a b : ℝ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
  ∑ i : Fin r, Matrix.single i.succ i.castSucc (a • (1 : F) - b • (RCLike.I : F))

private def rootFrequency (F : Type uF) [RCLike F] {r : ℕ} (a b : ℝ)
    (p : MatrixPositiveRoot (r + 1)) (k : Bool) : ℝ :=
  if ∃ i : Fin r, i.castSucc = p.val.1 ∧ i.succ = p.val.2 then
    a * RCLike.re (if k then RCLike.I else 1 : F) + b * RCLike.im (if k then RCLike.I else 1 : F)
  else 0

private theorem sum_rootFrequency_dual (a b : ℝ) :
    (∑ p : MatrixPositiveRoot (r + 1), ∑ k : Bool, rootFrequency F a b p k •
        matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k)) =
      matrixWhittakerLowerDirection F r a b := by
  classical
  let simple (p : MatrixPositiveRoot (r + 1)) :=
    ∃ i : Fin r, i.castSucc = p.val.1 ∧ i.succ = p.val.2
  let c := a • (1 : F) - b • (RCLike.I : F)
  have h_im : RCLike.im (RCLike.I : F) • (RCLike.I : F) = RCLike.I := by
    simpa only [RCLike.I_re, RCLike.ofReal_zero, zero_add, RCLike.real_smul_eq_coe_mul]
      using RCLike.re_add_im (RCLike.I : F)
  have hp (p : MatrixPositiveRoot (r + 1)) :
      (∑ k : Bool, rootFrequency F a b p k • matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k)) =
        if simple p then Matrix.single p.val.2 p.val.1 c else 0 := by
    by_cases h : simple p
    · simp only [h, ↓reduceIte, Fintype.sum_bool]
      simp only [rootFrequency, show ∃ i : Fin r, i.castSucc = p.val.1 ∧ i.succ = p.val.2 from h,
        ↓reduceIte, matrixTraceDualUnit, Bool.false_eq_true, RCLike.one_re,
        RCLike.one_im, RCLike.I_re, mul_zero, zero_add, mul_one, add_zero, Matrix.smul_single,
        mul_smul b (RCLike.im (RCLike.I : F)), smul_neg, h_im, ← Matrix.single_add]
      apply congrArg (Matrix.single p.val.2 p.val.1)
      rw [show c = a • (1 : F) + -(b • (RCLike.I : F)) from sub_eq_add_neg _ _]
      exact add_comm _ _
    · simp [rootFrequency, simple, h]
  simp_rw [hp]
  rw [← Finset.sum_filter]
  let e : Fin r ↪ MatrixPositiveRoot (r + 1) :=
    ⟨fun i => ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ⟩,
     fun _ _ h => Fin.castSucc_injective _ (congrArg (fun p : MatrixPositiveRoot (r + 1) => p.val.1) h)⟩
  have hs : Finset.univ.filter simple = Finset.univ.map e := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨i, h₁, h₂⟩
      exact ⟨i, Subtype.ext (Prod.ext h₁ h₂)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl, rfl⟩
  rw [hs, Finset.sum_map]
  rfl

private def matrixLeftTestDerivativeDirection (f : D) : M →ₗ[ℝ] D :=
  { toFun := fun X => matrixLeftTestDerivative X f
    map_add' := fun X Y => matrixLeftTestDerivative_add X Y f
    map_smul' := fun c X => matrixLeftTestDerivative_real_smul c X f }

/-- Upper-unipotent covariance makes the off-diagonal part of the
quadratic Casimir a first-order simple negative-root direction. -/
theorem matrixDistribution_traceCasimir_eq
    (T : D →L[ℂ] ℂ) (ψ : UnitaryAdditiveCharacter F) (a b : ℝ)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z))
    (hT : ∀ (u : upperUnipotent (r + 1) F) (f : D),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ r u : ℂ) * T f)
    (f : D) :
    T (matrixTraceTestCasimir F (r + 1) f) =
      T (matrixTraceDiagonalTestOperator F (r + 1) f) +
        (2 * Complex.I) * T (matrixLeftTestDerivative (matrixWhittakerLowerDirection F r a b) f) := by
  let L := (T.toLinearMap.restrictScalars ℝ).comp (matrixLeftTestDerivativeDirection f)
  have hsum :
      T (matrixLeftTestDerivative (matrixWhittakerLowerDirection F r a b) f) =
        ∑ p : MatrixPositiveRoot (r + 1), ∑ k : Bool,
          T (matrixLeftTestDerivative (rootFrequency F a b p k •
            matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k)) f) := by
    change L (matrixWhittakerLowerDirection F r a b) = ∑ p : MatrixPositiveRoot (r + 1), ∑ k : Bool,
      L (rootFrequency F a b p k • matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k))
    rw [← sum_rootFrequency_dual]
    simp only [map_sum]
  have hterm (p : MatrixPositiveRoot (r + 1)) (k : Bool) :
      T ((2 : ℕ) • matrixLeftTestDerivative (matrixTraceUnit F (r + 1) (p.val.1, p.val.2, k))
        (matrixLeftTestDerivative (matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k)) f)) =
      (2 * Complex.I) * T (matrixLeftTestDerivative (rootFrequency F a b p k •
        matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k)) f) := by
    let d := matrixTraceDualUnit F (r + 1) (p.val.1, p.val.2, k)
    have he : T (matrixLeftTestDerivative (matrixTraceUnit F (r + 1) (p.val.1, p.val.2, k))
        (matrixLeftTestDerivative d f)) =
        ((rootFrequency F a b p k : ℂ) * Complex.I) * T (matrixLeftTestDerivative d f) :=
      matrixDistribution_upperRootDerivative T ψ a b hψ hT p (if k then RCLike.I else 1)
        (matrixLeftTestDerivative d f)
    have hmap (c : ℝ) (g : D) : T (c • g) = c • T g := (T.restrictScalars ℝ).map_smul c g
    rw [map_nsmul, he, matrixLeftTestDerivative_real_smul, hmap]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, RCLike.real_smul_eq_coe_mul, d]
    let c : ℂ := rootFrequency F a b p k
    let x : ℂ := T (matrixLeftTestDerivative d f)
    change (2 : ℂ) * (c * Complex.I * x) = (2 * Complex.I) * (c * x)
    ring
  rw [matrixTraceTestCasimir_positive_roots, hsum]
  simp only [matrixTraceDiagonalTestOperator, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sum, hterm, Finset.sum_add_distrib, Finset.mul_sum]
  abel

end Langlands.Archimedean
