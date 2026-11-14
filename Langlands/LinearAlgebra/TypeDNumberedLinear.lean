import Langlands.LinearAlgebra.TypeDNumberedVectors

/-! # Independence and Cartan pairing of numbered type-D vectors -/

noncomputable section

namespace Langlands.TypeDNumberedVectors

variable {n : ℕ}

/-- The integral Gram matrix of the ordered simple vectors. -/
def simpleGramMatrix (hn : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => (simple hn i) ⬝ᵥ (simple hn j)

/-- The numbered integral type-D simple vectors are linearly independent. -/
theorem linearIndependent_simple (hn : 2 ≤ n) :
    LinearIndependent ℤ (simple hn) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let q : Fin n := ⟨n - 1, by omega⟩
  have hq (j : Fin n) :
      (if j.val + 1 < n then (0 : ℤ) else 2) = if j = q then 2 else 0 := by
    simp only [Fin.ext_iff]
    dsimp [q]
    split_ifs <;> omega
  have htotal := congrArg (TypeDParityLattice.coordinateSum (Fin n)) hc
  simp only [map_sum, map_zsmul, coordinateSum_simple, map_zero] at htotal
  simp_rw [hq] at htotal
  have hlast : c q = 0 := by
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      zsmul_eq_mul] at htotal
    norm_num at htotal
    omega
  by_cases hi : i.val + 1 < n
  · have hterm (j : Fin n) : c j • prefixSum i (simple hn j) =
        if j = i then c i else 0 := by
      by_cases hj : j = q
      · subst j
        have hqi : q ≠ i := by intro h; have := congrArg Fin.val h; dsimp [q] at this; omega
        simp [hlast, hqi]
      have hjn : j.val + 1 ≠ n := by
        intro h
        apply hj
        apply Fin.ext
        dsimp [q]
        omega
      rw [prefixSum_simple hn i j hi]
      by_cases hji : j = i
      · subst j
        simp [hjn]
      · simp [hji, hjn]
    have hp := congrArg (prefixSum i) hc
    simpa only [map_sum, map_zsmul, map_zero, hterm, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using hp
  · have : i = q := Fin.ext (by dsimp [q]; omega)
    simpa [this] using hlast

set_option maxHeartbeats 2000000 in
/-- The coordinate pairing has precisely the supplied type-D Cartan numbering. -/
theorem dotProduct_simple (hn : 4 ≤ n) (i j : Fin n) :
    (simple (by omega : 2 ≤ n) i) ⬝ᵥ (simple (by omega : 2 ≤ n) j) =
      CartanMatrix.D n i j := by
  by_cases hi : i.val + 1 < n <;> by_cases hj : j.val + 1 < n
  · rw [simple_chain _ i hi, simple_chain _ j hj]
    simp only [sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
      Pi.single_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · rw [simple_chain _ i hi]
    rw [show simple (by omega : 2 ≤ n) j =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 by simp [simple, hj]]
    simp only [sub_dotProduct, dotProduct_add, single_dotProduct, one_mul,
      Pi.single_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · rw [simple_chain _ j hj]
    rw [show simple (by omega : 2 ≤ n) i =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 by simp [simple, hi]]
    simp only [add_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
      Pi.single_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · rw [show simple (by omega : 2 ≤ n) i =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 by simp [simple, hi]]
    rw [show simple (by omega : 2 ≤ n) j =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 by simp [simple, hj]]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct, one_mul,
      Pi.single_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

/-- The Gram matrix agrees with Mathlib's type-D Cartan matrix in the given order. -/
theorem simpleGramMatrix_eq_D (hn : 4 ≤ n) :
    simpleGramMatrix (by omega : 2 ≤ n) = CartanMatrix.D n := by
  ext i j
  exact dotProduct_simple hn i j

end Langlands.TypeDNumberedVectors
