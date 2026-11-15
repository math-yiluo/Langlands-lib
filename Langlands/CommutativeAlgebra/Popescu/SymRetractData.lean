import Langlands.CommutativeAlgebra.Popescu.SymRetractAlgebra

/-! # The new relations of the symmetric-algebra retract after inverting a smooth element -/

namespace Langlands.CommutativeAlgebra.Popescu.SymRetract

open MvPolynomial

variable {R : Type*} [CommRing R] {n m : ℕ}

section Small

variable (F : Fin m → MvPolynomial (Fin n) R) (P : Matrix (Fin n) (Fin m) (MvPolynomial (Fin n) R))

/-- The matrix `E = D P`, where `D = (∂f_k/∂x_i)` is the Jacobian matrix of the `f_k`. -/
noncomputable def Et (k l : Fin m) : MvPolynomial (Fin n) R := ∑ i, pderiv i (F k) * P i l

variable (I : Ideal (MvPolynomial (Fin n) R)) (u : MvPolynomial (Fin n) R)

/-- `E D ≡ u D` modulo `I`. -/
theorem Et_mul_D_sub (hFI : ∀ k, F k ∈ I)
    (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2) (k : Fin m) (i : Fin n) :
    u * pderiv i (F k) - ∑ l, Et F P k l * pderiv i (F l) ∈ I := by
  have h := pderiv_mem_of_mem_sq I i (hE1 k)
  have hexp : pderiv i (u * F k - ∑ l, Et F P k l * F l) =
      (u * pderiv i (F k) - ∑ l, Et F P k l * pderiv i (F l)) +
        (F k * pderiv i u - ∑ l, F l * pderiv i (Et F P k l)) := by
    simp only [map_sub, map_sum, Derivation.leibniz, smul_eq_mul]
    rw [Finset.sum_add_distrib]
    ring
  rw [hexp] at h
  have h2 : F k * pderiv i u - ∑ l, F l * pderiv i (Et F P k l) ∈ I :=
    I.sub_mem (I.mul_mem_right _ (hFI k)) (I.sum_mem fun l _ => I.mul_mem_right _ (hFI l))
  simpa using I.sub_mem h h2

/-- `E² ≡ u E` modulo `I`. -/
theorem Et_sq_sub (hFI : ∀ k, F k ∈ I)
    (hE1 : ∀ k, u * F k - ∑ l, Et F P k l * F l ∈ I ^ 2) (k j : Fin m) :
    Et F P k j * u - ∑ l, Et F P k l * Et F P l j ∈ I := by
  have e1 : Et F P k j * u = ∑ i, u * pderiv i (F k) * P i j := by
    rw [Et, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ l, Et F P k l * Et F P l j =
      ∑ i, (∑ l, Et F P k l * pderiv i (F l)) * P i j := by
    calc ∑ l, Et F P k l * Et F P l j
        = ∑ l, ∑ i, Et F P k l * (pderiv i (F l) * P i j) :=
          Finset.sum_congr rfl fun l _ => by
            show Et F P k l * (∑ i, pderiv i (F l) * P i j) = _
            rw [Finset.mul_sum]
      _ = ∑ i, ∑ l, Et F P k l * (pderiv i (F l) * P i j) := Finset.sum_comm
      _ = ∑ i, (∑ l, Et F P k l * pderiv i (F l)) * P i j :=
          Finset.sum_congr rfl fun i _ => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun l _ => by ring
  have : Et F P k j * u - ∑ l, Et F P k l * Et F P l j =
      ∑ i, (u * pderiv i (F k) - ∑ l, Et F P k l * pderiv i (F l)) * P i j := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact I.sum_mem fun i _ => I.mul_mem_right _ (Et_mul_D_sub F P I u hFI hE1 k i)

end Small

section Big

variable (F : Fin m → MvPolynomial (Fin n) R) (P : Matrix (Fin n) (Fin m) (MvPolynomial (Fin n) R))
  (u : MvPolynomial (Fin n) R) (Θ : Fin m → Fin m → Fin m → MvPolynomial (Fin n) R)

/-- The relation `𝒢_k = u y_k − Σ_j E_kj y_j`. -/
noncomputable def Gk (k : Fin m) : MvPolynomial (Fin (n + m)) R :=
  symGen (fun j => (if k = j then u else 0) - Et F P k j)

/-- `Z̃_kp = Σ_j Θ_kjp y_j`. -/
noncomputable def Zt (k p : Fin m) : MvPolynomial (Fin (n + m)) R :=
  ∑ j, ιx (Θ k j p) * yv j

/-- The new relations `H_k = u³ f_k + u² 𝒢_k − Σ_p (E Z̃)_kp f_p`. -/
noncomputable def Hk (k : Fin m) : MvPolynomial (Fin (n + m)) R :=
  ιx u ^ 3 * ιx (F k) + ιx u ^ 2 * Gk F P u k -
    ∑ p, (∑ l, ιx (Et F P k l) * Zt Θ l p) * ιx (F p)

theorem Gk_eq (k : Fin m) : Gk F P u k =
    ιx u * yv k - ∑ j, ιx (Et F P k j) * yv j := by
  simp only [Gk, symGen, map_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The identity `E 𝒢 = Z̃ f`. -/
theorem Et_Gk (hΘ : ∀ k j, Et F P k j * u - ∑ l, Et F P k l * Et F P l j = ∑ p, Θ k j p * F p)
    (k : Fin m) :
    ∑ l, ιx (Et F P k l) * Gk F P u l = ∑ p, Zt Θ k p * ιx (F p) := by
  have h1 : ∀ j, ιx (m := m) (Et F P k j * u - ∑ l, Et F P k l * Et F P l j) * yv j =
      ∑ p, ιx (Θ k j p) * yv j * ιx (F p) := fun j => by
    rw [hΘ, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul]; ring
  calc ∑ l, ιx (Et F P k l) * Gk F P u l
      = ∑ j, ιx (m := m) (Et F P k j * u - ∑ l, Et F P k l * Et F P l j) * yv j := by
        simp only [Gk_eq, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, map_sub, map_mul,
          map_sum, sub_mul, Finset.sum_mul]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => by ring
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ p, Zt Θ k p * ιx (F p) := by
        simp only [h1, Zt, Finset.sum_mul]
        rw [Finset.sum_comm]

end Big

end Langlands.CommutativeAlgebra.Popescu.SymRetract
