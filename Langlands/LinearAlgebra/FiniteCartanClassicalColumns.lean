import Langlands.LinearAlgebra.FiniteCartanLeafExtension

/-! # Explicit positive columns for the classical finite Cartan matrices -/

open Matrix Finset

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

theorem sum_predecessor_sequence {n : ℕ} (Y : ℕ → ℤ)
    (hzero : Y 0 = 0) (i : Fin n) : (∑ j : Fin n, if j.val + 1 = i.val then Y (j.val + 1) else 0) =
      Y i.val := by
  by_cases hi : i.val = 0
  · simp [hi, hzero]
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    rw [Finset.sum_eq_single j]
    · have hj : j.val + 1 = i.val := by dsimp [j]; omega
      simp [hj]
    · intro b _ hbj
      have hne : b.val + 1 ≠ i.val := by
        intro h
        exact hbj (Fin.ext (by dsimp [j]; omega))
      simp [hne]
    · simp

theorem sum_successor_sequence {n : ℕ} (Y : ℕ → ℤ)
    (hend : Y (n + 1) = 0) (i : Fin n) : (∑ j : Fin n, if i.val + 1 = j.val then Y (j.val + 1) else 0) =
      Y (i.val + 2) := by
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, hi⟩
    rw [Finset.sum_eq_single j]
    · simp [j, Nat.add_assoc]
    · intro b _ hbj
      have hne : i.val + 1 ≠ b.val := by
        intro h
        exact hbj (Fin.ext h.symm)
      simp [hne]
    · simp
  · have heq : i.val + 2 = n + 1 := by omega
    rw [heq, hend]
    apply Finset.sum_eq_zero
    intro j _
    have hne : i.val + 1 ≠ j.val := by omega
    simp [hne]

theorem A_mulVec_sequence {n : ℕ} (Y : ℕ → ℤ)
    (hzero : Y 0 = 0) (hend : Y (n + 1) = 0) (i : Fin n) :
    (CartanMatrix.A n *ᵥ (fun j => Y (j.val + 1))) i =
      2 * Y (i.val + 1) - Y i.val - Y (i.val + 2) := by
  have hentry (j : Fin n) : CartanMatrix.A n i j =
      (if j = i then 2 else 0) -
      (if j.val + 1 = i.val then 1 else 0) -
      (if i.val + 1 = j.val then 1 else 0) := by
    simp only [CartanMatrix.A, Matrix.of_apply]
    split_ifs <;> grind
  simp only [Matrix.mulVec, dotProduct, hentry, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul, one_mul]
  rw [sum_predecessor_sequence Y hzero i, sum_successor_sequence Y hend i]
  simp

/-- A positive integral multiple of the `k`th inverse column of type A. -/
def A_columnSequence (n : ℕ) (k : Fin n) (t : ℕ) : ℤ :=
  if t ≤ k.val + 1 then (t : ℤ) * ((n : ℤ) - k.val)
  else ((k.val : ℤ) + 1) * ((n : ℤ) + 1 - t)

theorem A_columnSequence_recurrence {n : ℕ} (k i : Fin n) :
    2 * A_columnSequence n k (i.val + 1) -
      A_columnSequence n k i.val - A_columnSequence n k (i.val + 2) =
        if i = k then (n : ℤ) + 1 else 0 := by
  by_cases hik : i = k
  · subst i
    simp [A_columnSequence]
    ring
  · by_cases hlt : i.val < k.val
    · have h1 : i.val + 1 ≤ k.val + 1 := by omega
      have h0 : i.val ≤ k.val + 1 := by omega
      have h2 : i.val + 2 ≤ k.val + 1 := by omega
      simp [A_columnSequence, h0, h1, h2, hik]
      ring
    · have hgt : k.val < i.val := by
        have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
        omega
      by_cases hnext : i.val = k.val + 1
      · have h1 : ¬i.val + 1 ≤ k.val + 1 := by omega
        have h2 : ¬i.val + 2 ≤ k.val + 1 := by omega
        simp [A_columnSequence, hnext, hik]
        ring
      · have h0 : ¬i.val ≤ k.val + 1 := by omega
        have h1 : ¬i.val + 1 ≤ k.val + 1 := by omega
        have h2 : ¬i.val + 2 ≤ k.val + 1 := by omega
        simp [A_columnSequence, h0, h1, h2, hik]
        ring

theorem A_columnSequence_mulVec {n : ℕ} (k : Fin n) :
    CartanMatrix.A n *ᵥ (fun j => A_columnSequence n k (j.val + 1)) =
      fun j => if j = k then (n : ℤ) + 1 else 0 := by
  ext i
  rw [A_mulVec_sequence]
  · exact A_columnSequence_recurrence k i
  · simp [A_columnSequence]
  · have hn : ¬ n + 1 ≤ k.val + 1 := by omega
    simp [A_columnSequence, hn]

theorem A_columnSequence_nonneg {n : ℕ} (k i : Fin n) :
    0 ≤ A_columnSequence n k (i.val + 1) := by
  unfold A_columnSequence
  split_ifs
  · apply mul_nonneg <;> omega
  · apply mul_nonneg <;> omega

theorem leafExtension_A_bound {n : ℕ} {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.A n) k a b).IsFiniteCartan) (ha : a ≤ 0) :
    a * b * ((k.val : ℤ) + 1) * ((n : ℤ) - k.val) < 2 * ((n : ℤ) + 1) := by
  have hp := leafExtension_positive_bound hE ha
    (c := (n : ℤ) + 1) (by omega)
    (A_columnSequence_nonneg k) (A_columnSequence_mulVec k)
  simp [A_columnSequence] at hp
  nlinarith

theorem B_mulVec_sequence {n : ℕ} (Y : ℕ → ℤ)
    (hzero : Y 0 = 0) (hend : Y (n + 1) = 0) (i : Fin n) :
    (CartanMatrix.B n *ᵥ (fun j => Y (j.val + 1))) i =
      2 * Y (i.val + 1) - Y i.val - Y (i.val + 2) -
        (if i.val + 2 = n then Y (i.val + 2) else 0) := by
  have he (j : Fin n) : CartanMatrix.B n i j =
      CartanMatrix.A n i j -
        (if i.val + 2 = n then (if i.val + 1 = j.val then 1 else 0) else 0) := by
    simp only [CartanMatrix.A, CartanMatrix.B, Matrix.of_apply]
    split_ifs <;> grind
  simp only [Matrix.mulVec, dotProduct, he, sub_mul, Finset.sum_sub_distrib]
  change (CartanMatrix.A n *ᵥ (fun j => Y (j.val + 1))) i - _ = _
  rw [A_mulVec_sequence Y hzero hend]
  congr 1
  by_cases hi : i.val + 2 = n
  · simp only [hi, ite_true, ite_mul, one_mul, zero_mul]
    simpa only [hi] using sum_successor_sequence Y hend i
  · simp [hi]

theorem C_mulVec_sequence {n : ℕ} (Y : ℕ → ℤ)
    (hzero : Y 0 = 0) (hend : Y (n + 1) = 0) (i : Fin n) :
    (CartanMatrix.C n *ᵥ (fun j => Y (j.val + 1))) i =
      2 * Y (i.val + 1) - Y i.val - Y (i.val + 2) -
        (if i.val + 1 = n then Y i.val else 0) := by
  have he (j : Fin n) : CartanMatrix.C n i j =
      CartanMatrix.A n i j -
        (if i.val + 1 = n then (if j.val + 1 = i.val then 1 else 0) else 0) := by
    simp only [CartanMatrix.A, CartanMatrix.C, Matrix.of_apply]
    split_ifs <;> grind
  simp only [Matrix.mulVec, dotProduct, he, sub_mul, Finset.sum_sub_distrib]
  change (CartanMatrix.A n *ᵥ (fun j => Y (j.val + 1))) i - _ = _
  rw [A_mulVec_sequence Y hzero hend]
  congr 1
  by_cases hi : i.val + 1 = n
  · simp only [hi, ite_true, ite_mul, one_mul, zero_mul]
    exact sum_predecessor_sequence Y hzero i
  · simp [hi]

/-- Twice the inverse column for the upper-double-edge convention of type B. -/
def B_columnSequence (n : ℕ) (k : Fin n) (t : ℕ) : ℤ :=
  if t = n + 1 then 0 else
  if t = n then (if k.val + 1 = n then (n : ℤ) else (k.val : ℤ) + 1)
  else 2 * (min t (k.val + 1) : ℕ)

/-- Twice the inverse column for the lower-double-edge convention of type C. -/
def C_columnSequence (n : ℕ) (k : Fin n) (t : ℕ) : ℤ :=
  if t = n + 1 then 0 else
  if k.val + 1 = n then (t : ℤ) else 2 * (min t (k.val + 1) : ℕ)

theorem B_columnSequence_mulVec {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    CartanMatrix.B n *ᵥ (fun j => B_columnSequence n k (j.val + 1)) =
      fun j => if j = k then 2 else 0 := by
  ext i
  rw [B_mulVec_sequence]
  · have hi := i.isLt
    have hk := k.isLt
    simp only [B_columnSequence, Fin.ext_iff]
    split_ifs <;> omega
  · simp [B_columnSequence, show (0 : ℕ) ≠ n by omega]
  · simp [B_columnSequence]

theorem C_columnSequence_mulVec {n : ℕ} (hn : 2 ≤ n) (k : Fin n) :
    CartanMatrix.C n *ᵥ (fun j => C_columnSequence n k (j.val + 1)) =
      fun j => if j = k then 2 else 0 := by
  ext i
  rw [C_mulVec_sequence]
  · have hi := i.isLt
    have hk := k.isLt
    simp only [C_columnSequence, Fin.ext_iff]
    split_ifs <;> omega
  · have hnp : n ≠ 0 := by omega
    simp [C_columnSequence, hnp]
  · simp [C_columnSequence]

theorem B_columnSequence_nonneg {n : ℕ} (k i : Fin n) :
    0 ≤ B_columnSequence n k (i.val + 1) := by
  unfold B_columnSequence
  split_ifs <;> omega

theorem C_columnSequence_nonneg {n : ℕ} (k i : Fin n) :
    0 ≤ C_columnSequence n k (i.val + 1) := by
  unfold C_columnSequence
  split_ifs <;> omega

theorem leafExtension_B_bound {n : ℕ} (hn : 2 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.B n) k a b).IsFiniteCartan) (ha : a ≤ 0) :
    a * b * (if k.val + 1 = n then (n : ℤ) else 2 * ((k.val : ℤ) + 1)) < 4 := by
  have hp := leafExtension_positive_bound hE ha (c := 2) (by omega)
    (B_columnSequence_nonneg k) (B_columnSequence_mulVec hn k)
  have hk := k.isLt
  have he : B_columnSequence n k (k.val + 1) =
      if k.val + 1 = n then (n : ℤ) else 2 * ((k.val : ℤ) + 1) := by
    simp only [B_columnSequence]
    split_ifs <;> omega
  rw [he] at hp
  omega

theorem leafExtension_C_bound {n : ℕ} (hn : 2 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.C n) k a b).IsFiniteCartan) (ha : a ≤ 0) :
    a * b * (if k.val + 1 = n then (n : ℤ) else 2 * ((k.val : ℤ) + 1)) < 4 := by
  have hp := leafExtension_positive_bound hE ha (c := 2) (by omega)
    (C_columnSequence_nonneg k) (C_columnSequence_mulVec hn k)
  have hk := k.isLt
  have he : C_columnSequence n k (k.val + 1) =
      if k.val + 1 = n then (n : ℤ) else 2 * ((k.val : ℤ) + 1) := by
    simp only [C_columnSequence]
    split_ifs <;> omega
  rw [he] at hp
  omega

theorem sum_at_index_sequence {n : ℕ} (Y : ℕ → ℤ) (s : ℕ) (hs : s < n) :
    (∑ j : Fin n, if j.val = s then Y (j.val + 1) else 0) = Y (s + 1) := by
  have he (j : Fin n) : j.val = s ↔ j = ⟨s, hs⟩ := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp_rw [he]
  simp

theorem D_mulVec_sequence {n : ℕ} (hn : 4 ≤ n) (Y : ℕ → ℤ)
    (hzero : Y 0 = 0) (hend : Y (n + 1) = 0) (i : Fin n) :
    (CartanMatrix.D n *ᵥ (fun j => Y (j.val + 1))) i =
      2 * Y (i.val + 1) - Y i.val - Y (i.val + 2) +
        (if i.val = n - 2 then Y n else 0) +
        (if i.val = n - 1 then Y (n - 1) else 0) -
        (if i.val = n - 3 then Y n else 0) -
        (if i.val = n - 1 then Y (n - 2) else 0) := by
  have he (j : Fin n) : CartanMatrix.D n i j =
      CartanMatrix.A n i j +
        (if i.val = n - 2 ∧ j.val = n - 1 then 1 else 0) +
        (if i.val = n - 1 ∧ j.val = n - 2 then 1 else 0) -
        (if i.val = n - 3 ∧ j.val = n - 1 then 1 else 0) -
        (if i.val = n - 1 ∧ j.val = n - 3 then 1 else 0) := by
    simp only [CartanMatrix.A, CartanMatrix.D, Matrix.of_apply]
    split_ifs <;> grind
  simp only [Matrix.mulVec, dotProduct, he, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  change (CartanMatrix.A n *ᵥ (fun j => Y (j.val + 1))) i + _ + _ - _ - _ = _
  rw [A_mulVec_sequence Y hzero hend]
  simp only [ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel]
  rw [sum_at_index_sequence Y (n - 1) (by omega),
    sum_at_index_sequence Y (n - 2) (by omega),
    sum_at_index_sequence Y (n - 3) (by omega)]
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 2 + 1 = n - 1 := by omega
  have h3 : n - 3 + 1 = n - 2 := by omega
  rw [h1, h2, h3]
  simp

/-- Four times the inverse column of type D, in the standard fork numbering. -/
def D_columnSequence (n : ℕ) (k : Fin n) (t : ℕ) : ℤ :=
  if t = n + 1 then 0 else
  if k.val + 2 < n then
    (if t ≤ n - 2 then 4 * (min t (k.val + 1) : ℕ) else 2 * ((k.val : ℤ) + 1))
  else if t ≤ n - 2 then 2 * (t : ℤ)
  else if t = k.val + 1 then (n : ℤ) else (n : ℤ) - 2

theorem D_columnSequence_mulVec {n : ℕ} (hn : 4 ≤ n) (k : Fin n) :
    CartanMatrix.D n *ᵥ (fun j => D_columnSequence n k (j.val + 1)) =
      fun j => if j = k then 4 else 0 := by
  ext i
  rw [D_mulVec_sequence hn]
  · have hi := i.isLt
    have hk := k.isLt
    simp only [D_columnSequence, Fin.ext_iff]
    omega
  · have hnp : (0 : ℕ) ≠ n + 1 := by omega
    have hle : 0 ≤ n - 2 := Nat.zero_le _
    simp [D_columnSequence, hle]
  · simp [D_columnSequence]

theorem D_columnSequence_nonneg {n : ℕ} (hn : 4 ≤ n) (k i : Fin n) :
    0 ≤ D_columnSequence n k (i.val + 1) := by
  unfold D_columnSequence
  split_ifs <;> omega

theorem leafExtension_D_bound {n : ℕ} (hn : 4 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.D n) k a b).IsFiniteCartan) (ha : a ≤ 0) :
    a * b * (if k.val + 2 < n then 4 * ((k.val : ℤ) + 1) else (n : ℤ)) < 8 := by
  have hp := leafExtension_positive_bound hE ha (c := 4) (by omega)
    (D_columnSequence_nonneg hn k) (D_columnSequence_mulVec hn k)
  have hk := k.isLt
  have he : D_columnSequence n k (k.val + 1) =
      if k.val + 2 < n then 4 * ((k.val : ℤ) + 1) else (n : ℤ) := by
    simp only [D_columnSequence]
    split_ifs <;> omega
  rw [he] at hp
  omega

end Langlands.LinearAlgebra.FiniteCartanMatrix
