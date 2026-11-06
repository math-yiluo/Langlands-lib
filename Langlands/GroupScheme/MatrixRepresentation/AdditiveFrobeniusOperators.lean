import Langlands.GroupScheme.MatrixRepresentation.AdditiveTruncatedStability
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Mathlib.Algebra.Polynomial.Expand

/-! # Frobenius transforms of actual additive coefficient operators -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusOperators

open AdditiveDividedPowers AdditiveRestrictedOperators AdditiveTruncatedStability

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Apply the iterated coefficient-field Frobenius to an actual coefficient
matrix, then form its linear operator. -/
def frobeniusCoefficientOperator (e m : ℕ) : Module.End k (n → k) :=
  Matrix.toLin' ((coefficientMatrix ρ m).map (iterateFrobenius k p e))

/-- Postcomposition with the actual matrix Frobenius raises the polynomial
matrix entries to the iterated characteristic power. -/
theorem univariateMatrix_frobeniusPower (e : ℕ) :
    univariateMatrix (ρ.frobeniusPower p e) =
      (univariateMatrix ρ).map (fun f => f ^ p ^ e) := by
  let A := CommAlgCat.of k k[X]
  let x := VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
    (fun _ => (Polynomial.X : k[X]))
  have h := congrArg (fun M : Matrix.GeneralLinearGroup n k[X] =>
    (M : Matrix n n k[X])) (frobeniusPower_affineMatrix (p := p) ρ A x e)
  have hρ := univariateMatrix_aeval ρ A (Polynomial.X : k[X])
  have hτ := univariateMatrix_aeval (ρ.frobeniusPower p e) A (Polynomial.X : k[X])
  funext i j
  have hi := congrArg (fun M : Matrix n n k[X] => M i j) h
  have hiρ := congrArg (fun M : Matrix n n k[X] => M i j) hρ
  have hiτ := congrArg (fun M : Matrix n n k[X] => M i j) hτ
  change Polynomial.aeval (Polynomial.X : k[X]) (univariateMatrix ρ i j) = _ at hiρ
  change Polynomial.aeval (Polynomial.X : k[X])
    (univariateMatrix (ρ.frobeniusPower p e) i j) = _ at hiτ
  rw [Polynomial.aeval_X_left_apply] at hiρ hiτ
  rw [hiτ]
  change _ = (univariateMatrix ρ i j) ^ p ^ e
  exact hi.trans (congrArg (fun f : k[X] => f ^ p ^ e) hiρ.symm)

/-- In a degree divisible by p^e the original coefficient matrix is raised
entrywise to p^e. -/
theorem coefficientMatrix_frobeniusPower_mul (e m : ℕ) :
    coefficientMatrix (ρ.frobeniusPower p e) (p ^ e * m) =
      (coefficientMatrix ρ m).map (iterateFrobenius k p e) := by
  ext i j
  simp only [coefficientMatrix, univariateMatrix_frobeniusPower, Matrix.map_apply]
  rw [← Polynomial.map_iterateFrobenius_expand p _ e, Polynomial.coeff_map,
    Polynomial.coeff_expand_mul' (pow_pos (Fact.out : p.Prime).pos e)]

/-- All coefficients in degrees not divisible by p^e vanish. -/
theorem coefficientMatrix_frobeniusPower_of_not_dvd (e m : ℕ) (hm : ¬ p ^ e ∣ m) :
    coefficientMatrix (ρ.frobeniusPower p e) m = 0 := by
  ext i j
  simp only [coefficientMatrix, univariateMatrix_frobeniusPower, Matrix.map_apply]
  rw [← Polynomial.map_iterateFrobenius_expand p _ e, Polynomial.coeff_map,
    Polynomial.coeff_expand (pow_pos (Fact.out : p.Prime).pos e), ite_eq_right hm, map_zero]
  rfl

/-- The exact coefficient operator in degree p^e*m. Frobenius transforms
the coefficient entries as well as the degree. -/
theorem dividedPower_frobeniusPower_mul (e m : ℕ) :
    dividedPower (ρ.frobeniusPower p e) (p ^ e * m) =
      frobeniusCoefficientOperator ρ p e m := by
  rw [dividedPower_eq_toLin, coefficientMatrix_frobeniusPower_mul]
  rfl

/-- Coefficient operators outside the multiples of p^e vanish. -/
theorem dividedPower_frobeniusPower_of_not_dvd (e m : ℕ) (hm : ¬ p ^ e ∣ m) :
    dividedPower (ρ.frobeniusPower p e) m = 0 := by
  rw [dividedPower_eq_toLin, coefficientMatrix_frobeniusPower_of_not_dvd ρ p e m hm,
    map_zero]

/-- In particular, every positive coefficient below degree p^e vanishes. -/
theorem dividedPower_frobeniusPower_eq_zero_of_lt (e m : ℕ)
    (hmpos : 0 < m) (hm : m < p ^ e) :
    dividedPower (ρ.frobeniusPower p e) m = 0 := by
  apply dividedPower_frobeniusPower_of_not_dvd
  intro hdvd
  exact (Nat.not_le.mpr hm) (Nat.le_of_dvd hmpos hdvd)

/-- The first e characteristic-power operators of a Frobenius-powered
representation vanish. -/
theorem pPowerOperator_frobeniusPower_eq_zero_of_lt (e r : ℕ) (hr : r < e) :
    pPowerOperator (ρ.frobeniusPower p e) p r = 0 := by
  exact dividedPower_frobeniusPower_eq_zero_of_lt ρ p e (p ^ r)
    (pow_pos (Fact.out : p.Prime).pos r)
    ((Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mpr hr)

/-- Later characteristic-power operators are shifted, with coefficient-field
Frobenius applied entrywise. -/
theorem pPowerOperator_frobeniusPower_add (e r : ℕ) :
    pPowerOperator (ρ.frobeniusPower p e) p (e + r) =
      frobeniusCoefficientOperator ρ p e (p ^ r) := by
  rw [pPowerOperator, pow_add, dividedPower_frobeniusPower_mul]

/-- Every vector is fixed by the Frobenius-powered action at height e. -/
theorem truncatedFixedSubmodule_frobeniusPower (e : ℕ) :
    truncatedFixedSubmodule (ρ.frobeniusPower p e) (p ^ e) = ⊤ := by
  apply top_unique
  intro v _
  rw [mem_truncatedFixedSubmodule]
  intro m hmpos hm
  rw [dividedPower_frobeniusPower_eq_zero_of_lt ρ p e m hmpos hm]
  rfl

/-- All vectors from the coefficient field are fixed at every nilpotent
scalar of height e, over arbitrary test algebras. -/
theorem isFixedAtNilpotentScalars_frobeniusPower (e : ℕ) (v : n → k) :
    IsFixedAtNilpotentScalars (ρ.frobeniusPower p e) (p ^ e) v := by
  apply (mem_truncatedFixedSubmodule_iff_isFixedAtNilpotentScalars _ _ _).mp
  rw [truncatedFixedSubmodule_frobeniusPower]
  trivial

/-- The actual affine matrix is the identity at every scalar whose p^e-th
power vanishes, even in a nonreduced test algebra. -/
theorem affineMatrix_frobeniusPower_eq_one (e : ℕ) (A : CommAlgCat.{u} k)
    (t : A) (ht : t ^ p ^ e = 0) :
    ((ρ.frobeniusPower p e).affineMatrix A
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t)) :
        Matrix n n A) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have h := isFixedAtNilpotentScalars_frobeniusPower ρ p e
    (Pi.single j (1 : k)) A t ht
  have hsingle : (fun i => algebraMap k A ((Pi.single j (1 : k) : n → k) i)) =
      Pi.single j (1 : A) := by
    funext i
    simp [Pi.single_apply]
  rw [affineAction_apply, hsingle] at h
  simpa only [Matrix.one_mulVec] using h

/-- The action fixes every vector over the test algebra at height e. -/
theorem affineAction_frobeniusPower_eq_self (e : ℕ) (A : CommAlgCat.{u} k)
    (t : A) (ht : t ^ p ^ e = 0) (v : n → A) :
    (ρ.frobeniusPower p e).affineAction A
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t)) v = v := by
  rw [affineAction_apply, affineMatrix_frobeniusPower_eq_one ρ p e A t ht,
    Matrix.one_mulVec]

end Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusOperators
