import Langlands.LinearAlgebra.TypeDNumberedWeights
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-! # Integral normalization of numbered type-D vector weights -/

noncomputable section

open scoped BigOperators

namespace Langlands.TypeDVectorNormalization

variable {n : ℕ}

/-- The chain differences and the final sum determine each integral Gram row. -/
theorem gram_row (hn : 4 ≤ n) (i : Fin n) (v : Fin n → ℤ)
    (hchain : ∀ (j : Fin n) (hj : j.val + 1 < n),
      v j - v ⟨j.val + 1, hj⟩ = TypeDNumberedWeights.coefficient i j)
    (hlast : v ⟨n - 2, by omega⟩ + v ⟨n - 1, by omega⟩ =
      TypeDNumberedWeights.coefficient i ⟨n - 1, by omega⟩) :
    ∀ j, v j = if i = j then 1 else 0 := by
  let c := v ⟨0, by omega⟩ - if i.val = 0 then 1 else 0
  have hconstant : ∀ (d : ℕ) (hd : d < n),
      v ⟨d, hd⟩ - (if i.val = d then 1 else 0) = c := by
    intro d
    induction d with
    | zero => intro hd; rfl
    | succ d ih =>
      intro hd
      have hstep := hchain ⟨d, by omega⟩ hd
      have hprev := ih (by omega)
      simp only [TypeDNumberedWeights.coefficient, hd, ↓reduceIte,
        Fin.ext_iff] at hstep
      omega
  have hp := hconstant (n - 2) (by omega)
  have hq := hconstant (n - 1) (by omega)
  have hlast' : v ⟨n - 2, by omega⟩ + v ⟨n - 1, by omega⟩ =
      (if i.val = n - 2 then 1 else 0) + (if i.val = n - 1 then 1 else 0) := by
    rw [hlast]
    simp only [TypeDNumberedWeights.coefficient,
      show ¬ n - 1 + 1 < n by omega, ↓reduceIte]
    simp only [show (i.val + 2 = n) ↔ i.val = n - 2 by omega,
      show (i.val + 1 = n) ↔ i.val = n - 1 by omega]
  have hc : c = 0 := by omega
  intro j
  have hj := hconstant j.val j.isLt
  simpa only [Fin.eta, hc, sub_eq_zero, Fin.ext_iff] using hj

/-- Integral weights with the numbered type-D simple pairings are orthonormal. -/
theorem gram_eq (hn : 4 ≤ n) (x : Fin n → Fin n → ℤ)
    (hchain : ∀ (i j : Fin n) (hj : j.val + 1 < n),
      dotProduct (x i) (x j - x ⟨j.val + 1, hj⟩) =
        TypeDNumberedWeights.coefficient i j)
    (hlast : ∀ i, dotProduct (x i) (x ⟨n - 2, by omega⟩ + x ⟨n - 1, by omega⟩) =
      TypeDNumberedWeights.coefficient i ⟨n - 1, by omega⟩) :
    ∀ i j, dotProduct (x i) (x j) = if i = j then 1 else 0 := by
  intro i
  exact gram_row hn i (fun j => dotProduct (x i) (x j))
    (fun j hj => by simpa only [dotProduct_sub] using hchain i j hj)
    (by simpa only [dotProduct_add] using hlast i)

/-- An integral vector of squared norm one is a signed coordinate vector. -/
theorem exists_single_of_dotProduct_self_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℤ) (hv : dotProduct v v = 1) :
    ∃ (a : α) (s : ℤˣ), v = Pi.single a (s : ℤ) := by
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra! h
    simp [dotProduct, h] at hv
  have hbound : v a * v a ≤ 1 := by
    calc
      v a * v a ≤ ∑ j, v j * v j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ a)
      _ = 1 := hv
  have hs : v a = 1 ∨ v a = -1 := by
    have hlo : -1 ≤ v a := by nlinarith
    have hhi : v a ≤ 1 := by nlinarith
    omega
  have hsq : v a * v a = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hrest : ∑ j ∈ Finset.univ.erase a, v j * v j = 0 := by
    have h := Finset.sum_erase_add (s := Finset.univ) (f := fun j => v j * v j)
      (Finset.mem_univ a)
    change (∑ j, v j * v j) = 1 at hv
    omega
  have hsingle : v = Pi.single a (v a) := by
    funext j
    by_cases hj : j = a
    · simp [hj]
    · rw [Pi.single_eq_of_ne hj]
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (v j))).mp hrest j (by simp [hj])
      exact mul_self_eq_zero.mp h
  rcases hs with hs | hs
  · exact ⟨a, 1, by simpa [hs] using hsingle⟩
  · exact ⟨a, -1, by simpa [hs] using hsingle⟩

/-- An orthonormal integral family of full rank is a signed permutation of the coordinates. -/
theorem exists_signed_permutation (x : Fin n → Fin n → ℤ)
    (hgram : ∀ i j, dotProduct (x i) (x j) = if i = j then 1 else 0) :
    ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℤˣ),
      ∀ i, x i = Pi.single (σ i) (s i : ℤ) := by
  choose f s hs using fun i => exists_single_of_dotProduct_self_eq_one (x i)
    (by simpa using hgram i i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h := hgram i j
    simp only [hne, ↓reduceIte] at h
    rw [hs i, hs j, hij] at h
    simp [dotProduct, Pi.single_apply] at h
  exact ⟨Equiv.ofBijective f hf.bijective_of_finite, s, hs⟩

/-- Coordinate positions of an orthonormal integral family. -/
def permutation (x : Fin n → Fin n → ℤ)
    (hgram : ∀ i j, dotProduct (x i) (x j) = if i = j then 1 else 0) :
    Equiv.Perm (Fin n) :=
  Classical.choose (exists_signed_permutation x hgram)

/-- Coordinate signs of an orthonormal integral family. -/
def sign (x : Fin n → Fin n → ℤ)
    (hgram : ∀ i j, dotProduct (x i) (x j) = if i = j then 1 else 0) :
    Fin n → ℤˣ :=
  Classical.choose (Classical.choose_spec (exists_signed_permutation x hgram))

/-- The chosen positions and signs recover every original vector. -/
theorem normalization (x : Fin n → Fin n → ℤ)
    (hgram : ∀ i j, dotProduct (x i) (x j) = if i = j then 1 else 0) (i : Fin n) :
    x i = Pi.single (permutation x hgram i) (sign x hgram i : ℤ) :=
  Classical.choose_spec (Classical.choose_spec (exists_signed_permutation x hgram)) i

end Langlands.TypeDVectorNormalization
