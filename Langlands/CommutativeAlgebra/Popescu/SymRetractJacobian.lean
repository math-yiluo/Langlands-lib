import Langlands.CommutativeAlgebra.Popescu.SymRetractData

/-! # The Jacobian matrix of the new relations of the symmetric-algebra retract -/

namespace Langlands.CommutativeAlgebra.Popescu.SymRetract

open MvPolynomial

variable {R : Type*} [CommRing R] {n m : ℕ}
  (I : Ideal (MvPolynomial (Fin n) R)) (F : Fin m → MvPolynomial (Fin n) R)
  (P : Matrix (Fin n) (Fin m) (MvPolynomial (Fin n) R)) (u : MvPolynomial (Fin n) R)
  (Θ : Fin m → Fin m → Fin m → MvPolynomial (Fin n) R)

/-- The algebra `C = R[x, y]/J`. -/
def SymAlg : Type _ := MvPolynomial (Fin (n + m)) R ⧸ symIdeal I F

noncomputable instance : CommRing (SymAlg I F) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin (n + m)) R ⧸ symIdeal I F))

noncomputable instance : Algebra R (SymAlg I F) :=
  inferInstanceAs (Algebra R (MvPolynomial (Fin (n + m)) R ⧸ symIdeal I F))

/-- The quotient map onto `C`. -/
noncomputable def qC : MvPolynomial (Fin (n + m)) R →+* SymAlg I F := Ideal.Quotient.mk _

theorem qC_eq_zero_iff (x : MvPolynomial (Fin (n + m)) R) : qC I F x = 0 ↔ x ∈ symIdeal I F :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The image of `u` in `C`. -/
noncomputable abbrev uC : SymAlg I F := qC I F (ιx u)

/-- The matrix `E` over `C`. -/
noncomputable def EC : Matrix (Fin m) (Fin m) (SymAlg I F) :=
  Matrix.of fun k l => qC I F (ιx (Et F P k l))

/-- The Jacobian matrix `D` of the `f_k` over `C`. -/
noncomputable def DC : Matrix (Fin m) (Fin n) (SymAlg I F) :=
  Matrix.of fun k i => qC I F (ιx (pderiv i (F k)))

/-- The matrix `P` over `C`. -/
noncomputable def PC : Matrix (Fin n) (Fin m) (SymAlg I F) :=
  Matrix.of fun i l => qC I F (ιx (P i l))

/-- The matrix `Z̃` over `C`. -/
noncomputable def ZC : Matrix (Fin m) (Fin m) (SymAlg I F) :=
  Matrix.of fun k p => qC I F (Zt Θ k p)

/-- The `x`-derivatives `Ỹ` of the `𝒢_k` over `C`. -/
noncomputable def YC : Matrix (Fin m) (Fin n) (SymAlg I F) :=
  Matrix.of fun k i => qC I F (pderiv (Fin.castAdd m i) (Gk F P u k))

theorem qC_F (hFI : ∀ k, F k ∈ I) (k : Fin m) : qC I F (ιx (F k)) = 0 :=
  (qC_eq_zero_iff I F _).mpr (ιx_mem_symIdeal I F (hFI k))

theorem qC_Gk (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2) (k : Fin m) :
    qC I F (Gk F P u k) = 0 := by
  apply (qC_eq_zero_iff I F _).mpr
  apply symGen_mem_symIdeal
  have : ∑ j, ((if k = j then u else 0) - Et F P k j) * F j =
      u * F k - ∑ l, Et F P k l * F l := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [this]
  exact hE1 k

theorem EC_eq : EC I F P = DC I F * PC I F P := by
  ext k l
  simp [EC, DC, PC, Matrix.mul_apply, Et, map_sum, map_mul]

theorem EC_mul_DC (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2) :
    EC I F P * DC I F = uC I F u • DC I F := by
  ext k i
  have h := Et_mul_D_sub F P I u hFI hE1 k i
  have h' : qC I F (ιx (u * pderiv i (F k) - ∑ l, Et F P k l * pderiv i (F l))) = 0 :=
    (qC_eq_zero_iff I F _).mpr (ιx_mem_symIdeal I F h)
  simp only [map_sub, map_mul, map_sum] at h'
  simp only [Matrix.mul_apply, EC, DC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact (sub_eq_zero.mp h').symm

theorem EC_sq (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2) :
    EC I F P * EC I F P = uC I F u • EC I F P := by
  calc EC I F P * EC I F P = EC I F P * (DC I F * PC I F P) := by rw [← EC_eq]
    _ = (EC I F P * DC I F) * PC I F P := (Matrix.mul_assoc _ _ _).symm
    _ = uC I F u • EC I F P := by rw [EC_mul_DC I F P u hFI hE1, Matrix.smul_mul, ← EC_eq]

theorem ZC_mul_DC (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p) :
    ZC I F Θ * DC I F = EC I F P * YC I F P u := by
  ext k i
  have h := congrArg (fun z => qC I F (pderiv (Fin.castAdd m i) z)) (Et_Gk F P u Θ hΘ k)
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul, qC_Gk I F P u hE1,
    qC_F I F hFI, zero_mul, add_zero, pderiv_x_ιx] at h
  simp only [Matrix.mul_apply, ZC, DC, EC, YC, Matrix.of_apply]
  rw [← h]

theorem qC_pderiv_x_Hk (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (k : Fin m) (i : Fin n) :
    qC I F (pderiv (Fin.castAdd m i) (Hk F P u Θ k)) =
      (uC I F u ^ 3 • DC I F + uC I F u ^ 2 • YC I F P u - EC I F P * ZC I F Θ * DC I F) k i := by
  simp only [Hk, map_add, map_sub, map_sum, Derivation.leibniz, smul_eq_mul, map_mul,
    qC_F I F hFI, qC_Gk I F P u hE1, zero_mul, add_zero, pderiv_x_ιx,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, EC, ZC, DC, YC,
    Matrix.of_apply, map_pow, uC, Finset.sum_mul]

theorem qC_pderiv_y_Hk (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (k j : Fin m) :
    qC I F (pderiv (Fin.natAdd n j) (Hk F P u Θ k)) =
      (uC I F u ^ 2 • (uC I F u • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) - EC I F P)) k j := by
  have hG : pderiv (Fin.natAdd n j) (Gk F P u k) =
      ιx u * (if k = j then 1 else 0) - ιx (Et F P k j) := by
    rw [Gk_eq]
    simp only [map_sub, map_sum, Derivation.leibniz, smul_eq_mul, pderiv_y_ιx, pderiv_y_yv,
      mul_zero, add_zero, mul_ite, mul_one]
    rw [Finset.sum_ite_eq']
    simp
  simp only [Hk, map_add, map_sub, map_sum, Derivation.leibniz, smul_eq_mul, map_mul,
    qC_F I F hFI, qC_Gk I F P u hE1, mul_zero, zero_mul, add_zero, zero_add, hG, pderiv_y_ιx,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, EC, Matrix.of_apply, uC,
    map_pow, Finset.sum_const_zero, sub_zero]
  split_ifs <;> simp [mul_sub]

/-- The Jacobian matrix of the relations `H_k` over `C`. -/
noncomputable def JC : Matrix (Fin m) (Fin (n + m)) (SymAlg I F) :=
  Matrix.of fun k v => qC I F (pderiv v (Hk F P u Θ k))

/-- The right inverse (up to `u⁵`) of the Jacobian matrix of the `H_k`. -/
noncomputable def ΨC : Matrix (Fin (n + m)) (Fin m) (SymAlg I F) :=
  Matrix.of fun v l => Fin.addCases (motive := fun _ => SymAlg I F)
    (fun i => (uC I F u • PC I F P) i l)
    (fun j => (uC I F u ^ 2 • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) -
      YC I F P u * PC I F P) j l) v

theorem JC_mul_ΨC (hFI : ∀ k, F k ∈ I) (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2)
    (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p) :
    JC I F P u Θ * ΨC I F P u = uC I F u ^ 5 • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) := by
  set U := uC I F u
  have hsplit : JC I F P u Θ * ΨC I F P u =
      (U ^ 3 • DC I F + U ^ 2 • YC I F P u - EC I F P * ZC I F Θ * DC I F) * (U • PC I F P) +
      (U ^ 2 • (U • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) - EC I F P)) *
        (U ^ 2 • (1 : Matrix (Fin m) (Fin m) (SymAlg I F)) - YC I F P u * PC I F P) := by
    ext k l
    rw [Matrix.mul_apply, Fin.sum_univ_add, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [JC, ΨC, Matrix.of_apply, Fin.addCases_left]
      rw [qC_pderiv_x_Hk I F P u Θ hFI hE1]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [JC, ΨC, Matrix.of_apply, Fin.addCases_right]
      rw [qC_pderiv_y_Hk I F P u Θ hFI hE1]
  have hEZD : EC I F P * ZC I F Θ * DC I F = U • (EC I F P * YC I F P u) := by
    rw [Matrix.mul_assoc, ZC_mul_DC I F P u Θ hFI hE1 hΘ, ← Matrix.mul_assoc,
      EC_sq I F P u hFI hE1, Matrix.smul_mul]
  have hDP : DC I F * PC I F P = EC I F P := (EC_eq I F P).symm
  rw [hsplit, hEZD]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul, Matrix.mul_assoc, hDP]
  module

end Langlands.CommutativeAlgebra.Popescu.SymRetract
