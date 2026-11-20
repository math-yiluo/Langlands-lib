import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Representation.Archimedean.UnitaryFinitePolynomial
import Langlands.Representation.Archimedean.ComplexSwapJacquetDecay
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Trailing-row polynomials for compact-finite complex principal series -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "I" => Fin (n + 1)
local notation "G" => Langlands.GeneralLinear (n + 1) ℂ
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "Rect" => Matrix (Fin n) I ℂ
local notation "RectVar" => ((Fin n × I) ⊕ (Fin n × I))
local notation "SquareVar" => ((I × I) ⊕ (I × I))

/-- Build a square matrix from trailing rows `X` and the signed maximal minors of `Y`. -/
private def completeRows {R : Type*} [CommRing R] (X Y : Matrix (Fin n) I R) : Matrix I I R :=
  fun i j => Fin.cases ((-1) ^ (j : ℕ) * (Y.submatrix id j.succAbove).det) (fun r => X r j) i

private theorem completeRows_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (X Y : Matrix (Fin n) I R) : (completeRows X Y).map φ = completeRows (X.map φ) (Y.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp only [completeRows, map_apply, Fin.cases_zero, map_mul, map_pow, map_neg, map_one]
    rw [φ.map_det]
    rfl
  · rfl

/-- Complete the trailing rows using the conjugates of the missing-row cofactors. -/
def specialCompletion (X : Rect) : Matrix I I ℂ := completeRows X (X.map (starRingEnd ℂ))

private def leadingPhase (z : ℂˣ) : G := diagonalUnits (Fin.cons z 1)

private theorem star_det_eq_inv (k : K) : star k.val.val.det = (↑((determinant k.val)⁻¹) : ℂ) := by
  have hk := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary k.2)
  rw [Units.val_inv_eq_inv_val]
  change star k.val.val.det = k.val.val.det⁻¹
  exact eq_inv_of_mul_eq_one_left hk

private theorem leadingPhase_unitary {z : ℂˣ} (hz : (z : ℂ) ∈ unitary ℂ) :
    (leadingPhase z : G).val ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, leadingPhase, diagonalUnits_val, star_eq_conjTranspose,
    diagonal_conjTranspose, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    refine Fin.cases ?_ (fun r => ?_) i
    · simpa [Matrix.one_apply] using Unitary.mul_star_self_of_mem hz
    · simp
  · simp [h]

private theorem adjugate_unitary (k : K) : k.val.val.adjugate = k.val.val.det • k.val.valᴴ := by
  have hk : k.val.valᴴ * k.val.val = 1 := Unitary.star_mul_self_of_mem k.2
  calc
    _ = (k.val.valᴴ * k.val.val) * k.val.val.adjugate := by rw [hk, Matrix.one_mul]
    _ = k.val.valᴴ * (k.val.val * k.val.val.adjugate) := by rw [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

private theorem specialCompletion_trailingRows (k : K) :
    specialCompletion (trailingRows k.val.val) = (leadingPhase (determinant k.val)⁻¹ * k.val).val := by
  ext i j
  change _ = ((leadingPhase (determinant k.val)⁻¹).val * k.val.val : Matrix I I ℂ) i j
  rw [leadingPhase, diagonalUnits_val, Matrix.diagonal_mul]
  refine Fin.cases ?_ (fun r => ?_) i
  · simp only [specialCompletion, completeRows, Fin.cases_zero, Fin.cons_zero]
    have hminor : (trailingRows k.val.val).submatrix id j.succAbove =
        k.val.val.submatrix (0 : I).succAbove j.succAbove := by
      ext r t
      simp [trailingRows, Matrix.submatrix_apply]
    rw [show (((trailingRows k.val.val).map (starRingEnd ℂ)).submatrix id j.succAbove).det =
      star ((trailingRows k.val.val).submatrix id j.succAbove).det from
        ((starRingEnd ℂ).map_det _).symm, hminor]
    have h : star (k.val.val.adjugate j 0) =
        (-1 : ℂ) ^ (j : ℕ) * star (k.val.val.submatrix (0 : I).succAbove j.succAbove).det := by
      rw [adjugate_fin_succ_eq_det_submatrix]
      simp
    rw [← h, adjugate_unitary, Matrix.smul_apply, smul_eq_mul, star_mul, conjTranspose_apply,
      star_star, star_det_eq_inv, mul_comm]
  · simp [specialCompletion, completeRows, trailingRows]

/-- The completion of the trailing rows of a unitary matrix is special unitary. -/
theorem specialCompletion_mem_specialUnitaryGroup (k : K) :
    specialCompletion (trailingRows k.val.val) ∈ Matrix.specialUnitaryGroup I ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, specialCompletion_trailingRows]
  constructor
  · apply (Matrix.unitaryGroup I ℂ).mul_mem _ k.2
    apply leadingPhase_unitary
    rw [← star_det_eq_inv k]
    exact Unitary.star_mem (Matrix.det_of_mem_unitary k.2)
  · rw [Units.val_mul, Matrix.det_mul, leadingPhase, diagonalUnits_val, Matrix.det_diagonal,
      Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.one_apply, Units.val_one, Finset.prod_const_one, mul_one]
    change (↑((determinant k.val)⁻¹) : ℂ) * (determinant k.val : ℂ) = 1
    exact Units.inv_mul _

/-- Evaluation of the rectangular entries and their conjugates. -/
def rectangularCoordValue (X : Rect) : RectVar → ℂ :=
  Sum.elim (fun ij => X ij.1 ij.2) (fun ij => star (X ij.1 ij.2))

private def squareCoordValue (A : Matrix I I ℂ) : SquareVar → ℂ :=
  Sum.elim (fun ij => A ij.1 ij.2) (fun ij => star (A ij.1 ij.2))

private def entryPolynomials : SquareVar → MvPolynomial RectVar ℂ :=
  let U : Matrix (Fin n) I (MvPolynomial RectVar ℂ) := fun i j => MvPolynomial.X (.inl (i, j))
  let V : Matrix (Fin n) I (MvPolynomial RectVar ℂ) := fun i j => MvPolynomial.X (.inr (i, j))
  Sum.elim (fun ij => completeRows U V ij.1 ij.2) (fun ij => completeRows V U ij.1 ij.2)

private theorem eval_entryPolynomials (X : Rect) (j : SquareVar) :
    MvPolynomial.eval (rectangularCoordValue X) (entryPolynomials j) =
      squareCoordValue (specialCompletion X) j := by
  let U : Matrix (Fin n) I (MvPolynomial RectVar ℂ) := fun i j => MvPolynomial.X (.inl (i, j))
  let V : Matrix (Fin n) I (MvPolynomial RectVar ℂ) := fun i j => MvPolynomial.X (.inr (i, j))
  let φ := MvPolynomial.eval (rectangularCoordValue X)
  have hU : U.map φ = X := by ext i j; simp [U, φ, rectangularCoordValue]
  have hV : V.map φ = X.map (starRingEnd ℂ) := by ext i j; simp [V, φ, rectangularCoordValue]
  have hstar : ((X.map (starRingEnd ℂ)).map (starRingEnd ℂ)) = X := by ext i j; simp
  rcases j with ij | ij
  · change ((completeRows U V).map φ) ij.1 ij.2 = (specialCompletion X) ij.1 ij.2
    rw [completeRows_map, hU, hV, specialCompletion]
  · change ((completeRows V U).map φ) ij.1 ij.2 = star ((specialCompletion X) ij.1 ij.2)
    rw [completeRows_map, hU, hV]
    change _ = ((completeRows X (X.map (starRingEnd ℂ))).map (starRingEnd ℂ)) ij.1 ij.2
    rw [completeRows_map, hstar]

private theorem eval_pulledBackPolynomial (P : MvPolynomial SquareVar ℂ) (X : Rect) :
    MvPolynomial.eval (rectangularCoordValue X) (MvPolynomial.bind₁ entryPolynomials P) =
      MvPolynomial.eval (squareCoordValue (specialCompletion X)) P := by
  simp only [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
  congr 2
  funext j
  exact eval_entryPolynomials X j

private theorem leadingPhase_covariance (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (n + 1) (d :: ds))
    (k : K) : f (leadingPhase (determinant k.val)⁻¹ * k.val) =
      (d.character (determinant k.val) : ℂ)⁻¹ * f k.val := by
  let a : I → ℂˣ := Fin.cons (determinant k.val)⁻¹ 1
  have h := hf.2 a (1 : upperUnipotent (n + 1) ℂ) k.val
  simp only [Subgroup.coe_one, mul_one] at h
  have hnorm : ‖(↑((determinant k.val)⁻¹) : ℂ)‖ = 1 := by
    have hs := normSqC_det_unitary k
    change ((‖(determinant k.val : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 at hs
    have hsq : ‖(determinant k.val : ℂ)‖ ^ 2 = (1 : ℝ) := by exact_mod_cast hs
    have hd := (sq_eq_sq₀ (norm_nonneg (determinant k.val : ℂ)) zero_le_one).mp
      (by simpa only [one_pow] using hsq)
    rw [Units.val_inv_eq_inv_val, norm_inv, hd, inv_one]
  rw [principalSeriesCharacter, Fin.prod_univ_succ] at h
  simp only [a, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, complexPositionCharacter,
    Pi.one_apply, Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow,
    ComplexSwapJacquet.complexPositionCharacter_one, mul_one, Finset.prod_const_one] at h
  rw [hnorm, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  simpa only [leadingPhase, map_inv, Units.val_inv_eq_inv_val] using h

/-- The compact restriction of a standard vector, divided by its distinguished determinant
character, is a polynomial in the trailing rows and their conjugates. -/
def ComplexGodementTrailingPolynomialStatement : Prop :=
  ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : G → ℂ),
    f ∈ complexStandardModule (n + 1) (d :: ds) →
    f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K →
    ∃ Q : MvPolynomial RectVar ℂ, ∀ k : K,
      MvPolynomial.eval (rectangularCoordValue (trailingRows k.val.val)) Q =
        (d.character (determinant k.val) : ℂ)⁻¹ * f k.val

theorem complexGodementTrailingPolynomial : ComplexGodementTrailingPolynomialStatement (n := n) := by
  intro d ds f hf hfinite
  obtain ⟨P, hP⟩ := UnitaryFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors
    hf.1.continuous hfinite 1
  refine ⟨MvPolynomial.bind₁ entryPolynomials P, fun k => ?_⟩
  let g := leadingPhase (determinant k.val)⁻¹ * k.val
  have hg := (Matrix.mem_specialUnitaryGroup_iff.mp (specialCompletion_mem_specialUnitaryGroup k)).1
  rw [specialCompletion_trailingRows] at hg
  let k' : Matrix.unitaryGroup I ℂ := ⟨g.val, hg⟩
  have hk' : Unitary.toUnits k' = g := Units.ext rfl
  rw [eval_pulledBackPolynomial, specialCompletion_trailingRows]
  change MvPolynomial.eval (UnitaryFinitePolynomial.coordValue k') P = _
  rw [← hP k', one_mul, hk']
  exact leadingPhase_covariance d ds hf k

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
