import Langlands.GroupScheme.MatrixRepresentation.VectorGroupPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Taylor

/-! # Divided-power operators of actual additive-group representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers

open VectorGroupPolynomial

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- The universal matrix of an additive-group representation in one polynomial variable. -/
def univariateMatrix : Matrix n n k[X] :=
  (polynomialMatrix ρ).map (MvPolynomial.uniqueAlgEquiv k (Fin 1))

theorem univariateMatrix_aeval (S : CommAlgCat.{u} k) (t : S) :
    (univariateMatrix ρ).map (Polynomial.aeval t) =
      (ρ.affineMatrix S
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) S (fun _ => t)) :
          Matrix n n S) := by
  rw [← polynomialMatrix_aeval ρ S (fun _ => t)]
  ext i j
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv

/-- The representation law, evaluated over an arbitrary commutative test algebra. -/
theorem univariateMatrix_add (S : CommAlgCat.{u} k) (s t : S) :
    (univariateMatrix ρ).map (Polynomial.aeval (s + t)) =
      (univariateMatrix ρ).map (Polynomial.aeval s) *
        (univariateMatrix ρ).map (Polynomial.aeval t) := by
  rw [univariateMatrix_aeval, univariateMatrix_aeval, univariateMatrix_aeval]
  have h := VectorGroup.affinePoint_add (R := CommRingCat.of k) (d := 1) S
    (fun _ => s) (fun _ => t)
  have h' := congrArg (fun x => (ρ.affineMatrix S x : Matrix n n S)) h
  rw [map_mul] at h'
  exact h'

/-- The degree-indexed coefficient matrices of the actual universal matrix. -/
def coefficientMatrix (m : ℕ) : Matrix n n k :=
  fun i j => (univariateMatrix ρ i j).coeff m

/-- The divided-power coefficient operators, defined directly from the actual representation. -/
def dividedPower (m : ℕ) : Module.End k (n → k) :=
  coefficientOperators ρ (Finsupp.single (0 : Fin 1) m)

theorem dividedPower_eq_toLin (m : ℕ) :
    dividedPower ρ m = Matrix.toLin' (coefficientMatrix ρ m) := by
  rw [dividedPower, coefficientOperators_apply]
  congr 1
  ext i j
  exact (MvPolynomial.coeff_uniqueAlgEquiv k _ m).symm

section ScalarCoefficients

variable (P Q : k[X]) (a b : ℕ)

private theorem aeval_outer :
    Polynomial.aeval (Polynomial.X : k[X][X]) P = P.map Polynomial.C := by
  exact Polynomial.aeval_X_left_eq_map P

private theorem aeval_inner :
    Polynomial.aeval (Polynomial.C (Polynomial.X : k[X]) : k[X][X]) P =
      Polynomial.C P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial m c =>
    simp [← Polynomial.C_mul_X_pow_eq_monomial]

private theorem aeval_sum :
    Polynomial.aeval (Polynomial.X + Polynomial.C (Polynomial.X : k[X]) : k[X][X]) P =
      Polynomial.taylor Polynomial.X (P.map Polynomial.C) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.map_add, hP, hQ]
  | monomial m c =>
    simp [Polynomial.aeval_monomial, Polynomial.taylor_monomial]

private theorem coeff_aeval_sum :
    ((Polynomial.aeval
        (Polynomial.X + Polynomial.C (Polynomial.X : k[X]) : k[X][X]) P).coeff a).coeff b =
      (Nat.choose (a + b) a : k) * P.coeff (a + b) := by
  rw [aeval_sum, Polynomial.taylor_coeff, Polynomial.hasseDeriv_map,
    Polynomial.eval_map, Polynomial.eval₂_C_X, Polynomial.hasseDeriv_coeff, Nat.add_comm b a]

private theorem coeff_aeval_product :
    ((Polynomial.aeval (Polynomial.X : k[X][X]) P *
        Polynomial.aeval (Polynomial.C (Polynomial.X : k[X]) : k[X][X]) Q).coeff a).coeff b =
      P.coeff a * Q.coeff b := by
  rw [aeval_outer, aeval_inner, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    Polynomial.coeff_C_mul]

end ScalarCoefficients

/-- The constant coefficient of the actual representation matrix is the identity. -/
theorem coefficientMatrix_zero : coefficientMatrix ρ 0 = 1 := by
  have h := univariateMatrix_aeval ρ (CommAlgCat.of k k) 0
  rw [show (fun _ : Fin 1 => (0 : k)) = 0 from rfl,
    VectorGroup.affinePoint_zero, map_one] at h
  ext i j
  change (univariateMatrix ρ i j).coeff 0 = (1 : Matrix n n k) i j
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact congrArg (fun M : Matrix n n k => M i j) h

/-- Matrix coefficients of an actual additive-group action satisfy the divided-power law. -/
theorem coefficientMatrix_mul (a b : ℕ) :
    coefficientMatrix ρ a * coefficientMatrix ρ b =
      (Nat.choose (a + b) a : k) • coefficientMatrix ρ (a + b) := by
  have h := univariateMatrix_add ρ (CommAlgCat.of k k[X][X])
    (Polynomial.X : k[X][X]) (Polynomial.C (Polynomial.X : k[X]))
  ext i j
  have hij := congrArg (fun M : Matrix n n k[X][X] => (M i j).coeff a |>.coeff b) h
  change ((Polynomial.aeval (Polynomial.X + Polynomial.C Polynomial.X)
      (univariateMatrix ρ i j)).coeff a).coeff b =
    ((∑ l, Polynomial.aeval Polynomial.X (univariateMatrix ρ i l) *
      Polynomial.aeval (Polynomial.C Polynomial.X) (univariateMatrix ρ l j)).coeff a).coeff b at hij
  simp only [coeff_aeval_sum, Polynomial.finsetSum_coeff, coeff_aeval_product] at hij
  exact hij.symm

@[simp] theorem dividedPower_zero : dividedPower ρ 0 = 1 := by
  rw [dividedPower_eq_toLin, coefficientMatrix_zero, Matrix.toLin'_one]
  rfl

/-- Composition of actual additive-group coefficient operators is a binomial multiple. -/
theorem dividedPower_mul (a b : ℕ) :
    dividedPower ρ a * dividedPower ρ b =
      (Nat.choose (a + b) a : k) • dividedPower ρ (a + b) := by
  simp only [dividedPower_eq_toLin]
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, coefficientMatrix_mul, map_smul]

/-- The coefficient operators commute, over finite as well as infinite fields. -/
theorem dividedPower_commute (a b : ℕ) :
    dividedPower ρ a * dividedPower ρ b = dividedPower ρ b * dividedPower ρ a := by
  rw [dividedPower_mul, dividedPower_mul, Nat.add_comm b a, Nat.choose_symm_add]

/-- Only finitely many degree-indexed operators are nonzero. -/
theorem dividedPower_eventually_zero :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → dividedPower ρ m = 0 := by
  classical
  let N := (coefficientOperators ρ).support.sup (fun a => a 0) + 1
  refine ⟨N, fun m hm => ?_⟩
  change coefficientOperators ρ (Finsupp.single (0 : Fin 1) m) = 0
  apply Finsupp.notMem_support_iff.mp
  intro h
  have hle := Finset.le_sup (f := fun a : Fin 1 →₀ ℕ => a 0) h
  simp only [Finsupp.single_eq_same] at hle
  dsimp [N] at hm
  omega

/-- A power of the first operator is its factorial multiple of the corresponding coefficient. -/
theorem dividedPower_one_pow (m : ℕ) :
    dividedPower ρ 1 ^ m = (m.factorial : k) • dividedPower ρ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, mul_smul_comm, dividedPower_mul, smul_smul,
      Nat.add_comm 1 m, Nat.choose_one_right, Nat.factorial_succ]
    congr 1
    push_cast
    ring

end Langlands.GroupScheme.MatrixRepresentation.AdditiveDividedPowers
