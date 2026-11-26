import Langlands.Global.RankinSelberg.ComplexEqualGaussianChamber

/-! # Last-row separation of standard square Gaussian tests -/

noncomputable section

open MvPolynomial
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexGodementGaussianPolynomial (Coordinates coordinates matrixSqNorm standardMatrixTest
  standardMatrixTest_apply standardColumnTest scalePolynomial)
open ComplexSquareZeta (squarePolynomialGaussian)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "scale" => (2 * Real.pi : ℝ)

private def rowCoords {n : ℕ} (v : Fin n → ℂ) (j : Fin n × Bool) : ℂ :=
  if j.2 then (v j.1).im else (v j.1).re

private theorem exists_scalePolynomial_preimage {ι : Type*} (p : MvPolynomial ι ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ c : ι → ℂ, eval c (scalePolynomial q) = eval c p := by
  let u : ℂ := Real.sqrt scale
  have hu : u ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  let q := bind₁ (fun j : ι => C u⁻¹ * X j) p
  refine ⟨q, fun c => ?_⟩
  change aeval c (bind₁ (fun j : ι => C u * X j) q) = aeval c p
  rw [aeval_bind₁]
  change aeval _ (bind₁ (fun j : ι => C u⁻¹ * X j) p) = _
  rw [aeval_bind₁]
  congr 2
  funext j
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, ← mul_assoc,
    inv_mul_cancel₀ hu, one_mul]

private theorem exists_rowGaussian {r : ℕ} (p : MvPolynomial (Fin (r + 1) × Bool) ℂ) :
    ∃ φ : 𝓢(Fin (r + 1) → ℂ, ℂ), ∀ v, φ v =
      eval (rowCoords v) p * (Real.exp (-scale * ∑ j, ‖v j‖ ^ 2) : ℂ) := by
  let q := rename (fun j : Fin (r + 1) × Bool => (j.1, (0 : Fin 1), j.2)) p
  obtain ⟨Q, hQ⟩ := exists_scalePolynomial_preimage q
  refine ⟨standardColumnTest Q, fun v => ?_⟩
  let A : Mat (r + 1) 1 := Matrix.of fun i _ => v i
  change standardMatrixTest Q A = _
  rw [standardMatrixTest_apply, hQ, eval_rename]
  have hC : coordinates A ∘ (fun j : Fin (r + 1) × Bool => (j.1, (0 : Fin 1), j.2)) = rowCoords v := by
    funext j
    obtain ⟨i, b⟩ := j
    cases b <;> rfl
  rw [hC]
  have hN : matrixSqNorm A = ∑ j, ‖v j‖ ^ 2 := by
    simp only [matrixSqNorm, Fin.sum_univ_one, A, Matrix.of_apply]
  rw [hN]

variable {m : ℕ}
local notation "n" => (m + 1 : ℕ)
local notation "Square" => Mat n n
local notation "Row" => Fin n → ℂ
local notation "Poly" => MvPolynomial (Coordinates n n) ℂ
local notation "RectPoly" => MvPolynomial (Coordinates m n) ℂ
local notation "RowPoly" => MvPolynomial (Fin n × Bool) ℂ

private theorem exists_eval_row_split (p : Poly) :
    ∃ (l : ℕ) (P : Fin l → RectPoly) (q : Fin l → RowPoly),
      ∀ A : Square, eval (coordinates A) p = ∑ j,
        eval (coordinates (complexSquareFirstRows A)) (P j) * eval (rowCoords (A (Fin.last m))) (q j) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact ⟨1, fun _ => C a, fun _ => 1, by simp⟩
  | add p q hp hq =>
    obtain ⟨l, P, Q, hp⟩ := hp
    obtain ⟨l', P', Q', hq⟩ := hq
    refine ⟨l + l', Fin.addCases P P', Fin.addCases Q Q', fun A => ?_⟩
    rw [map_add, hp, hq, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
  | mul_X p i hp =>
    obtain ⟨l, P, q, hp⟩ := hp
    obtain ⟨i, j, b⟩ := i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine ⟨l, P, fun k => q k * X (j, b), fun A => ?_⟩
      rw [map_mul, eval_X, hp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, eval_X, mul_assoc]
      congr 2
      cases b <;> rfl
    · refine ⟨l, fun k => P k * X (i, j, b), q, fun A => ?_⟩
      rw [map_mul, eval_X, hp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_mul, eval_X, mul_assoc]
      congr 1
      rw [show coordinates (complexSquareFirstRows A) (i, j, b) = coordinates A (i.castSucc, j, b) from rfl]
      exact mul_comm _ _

/-- Every standard square polynomial Gaussian is a finite sum of products of standard
rectangular polynomial Gaussians on the first rows and standard polynomial Gaussians on the
last row. -/
def ComplexSquareGaussianRowSplitStatement : Prop :=
  ∀ p : Poly,
    ∃ (l : ℕ) (P : Fin l → RectPoly) (φ : Fin l → 𝓢(Row, ℂ)),
      (∀ j, IsGaussianPolynomialRow scale (φ j)) ∧
      ∀ A : Square, squarePolynomialGaussian p A = ∑ j,
        complexSquareProductTest (operatorToEntry (standardMatrixTest (P j))) (φ j) A

theorem complexSquareGaussianRowSplit : ComplexSquareGaussianRowSplitStatement (m := m) := by
  intro p
  obtain ⟨l, P, q, hp⟩ := exists_eval_row_split p
  choose P' hP' using fun j => exists_scalePolynomial_preimage (P j)
  choose φ hφ using fun j => exists_rowGaussian (q j)
  refine ⟨l, P', φ, fun j => ⟨q j, hφ j⟩, fun A => ?_⟩
  let Y := complexSquareFirstRows A
  let v := A (Fin.last m)
  have hNorm : matrixSqNorm A = matrixSqNorm Y + ∑ j, ‖v j‖ ^ 2 := by
    rw [matrixSqNorm, Fin.sum_univ_castSucc]
    rfl
  change eval (coordinates A) p * (Real.exp (-scale * matrixSqNorm A) : ℂ) = _
  rw [hp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = standardMatrixTest (P' j) Y * φ j v
  rw [standardMatrixTest_apply, hP', hφ, hNorm, mul_add, Real.exp_add, Complex.ofReal_mul]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
