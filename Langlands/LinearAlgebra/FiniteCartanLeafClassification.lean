import Langlands.LinearAlgebra.FiniteCartanLeafNumberings

/-! # Allowed leaf extensions of standard finite Cartan matrices -/

open Matrix

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

theorem hasCartanMatrix_self {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ) :
    HasCartanMatrix N N :=
  ⟨Equiv.refl _, fun _ _ => rfl⟩

theorem hasType_A {n : ℕ} (hn : 1 ≤ n) :
    HasIrreducibleCartanType (CartanMatrix.A n) :=
  Or.inl ⟨n, hn, hasCartanMatrix_self _⟩

theorem hasType_B {n : ℕ} (hn : 2 ≤ n) :
    HasIrreducibleCartanType (CartanMatrix.B n) :=
  Or.inr (Or.inl ⟨n, hn, hasCartanMatrix_self _⟩)

theorem hasType_C {n : ℕ} (hn : 2 ≤ n) :
    HasIrreducibleCartanType (CartanMatrix.C n) :=
  Or.inr (Or.inr (Or.inl ⟨n, hn, hasCartanMatrix_self _⟩))

theorem hasType_D {n : ℕ} (hn : 4 ≤ n) :
    HasIrreducibleCartanType (CartanMatrix.D n) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hasCartanMatrix_self _⟩)))

theorem hasType_E6 : HasIrreducibleCartanType (CartanMatrix.E 6) := by
  unfold HasIrreducibleCartanType
  right
  right
  right
  right
  left
  exact hasCartanMatrix_self _

theorem hasType_E7 : HasIrreducibleCartanType (CartanMatrix.E 7) := by
  unfold HasIrreducibleCartanType
  right
  right
  right
  right
  right
  left
  exact hasCartanMatrix_self _

theorem hasType_E8 : HasIrreducibleCartanType (CartanMatrix.E 8) := by
  unfold HasIrreducibleCartanType
  right
  right
  right
  right
  right
  right
  left
  exact hasCartanMatrix_self _

theorem hasType_F4 : HasIrreducibleCartanType (CartanMatrix.F₄) := by
  unfold HasIrreducibleCartanType
  right
  right
  right
  right
  right
  right
  right
  left
  exact hasCartanMatrix_self _

theorem hasType_G2 : HasIrreducibleCartanType (CartanMatrix.G₂) := by
  unfold HasIrreducibleCartanType
  right
  right
  right
  right
  right
  right
  right
  right
  exact hasCartanMatrix_self _

theorem A_simple_bound_cases {n k : ℕ} (hk : k < n)
    (h : ((k : ℤ) + 1) * ((n : ℤ) - k) < 2 * ((n : ℤ) + 1)) :
    k = 0 ∨ k + 1 = n ∨ k = 1 ∨ k + 2 = n ∨
      (5 ≤ n ∧ n ≤ 7 ∧ (k = 2 ∨ k + 3 = n)) := by
  by_cases hleft : k ≤ 1
  · omega
  by_cases hright : n ≤ k + 2
  · omega
  have hlow : 2 ≤ k := by omega
  have hhigh : k + 3 ≤ n := by omega
  have hnear : k = 2 ∨ k + 3 = n := by
    by_contra hne
    have hklow : 3 ≤ k := by omega
    have hnhigh : k + 4 ≤ n := by omega
    have hpos : 0 ≤ ((k : ℤ) - 3) * ((n : ℤ) - k - 4) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have hn : n ≤ 7 := by
    rcases hnear with hnear | hnear
    · subst k
      norm_num at h
      omega
    · have he : (n : ℤ) - k = 3 := by omega
      rw [he] at h
      nlinarith
  omega

theorem A_double_bound_cases {n k : ℕ} (hk : k < n)
    (h : 2 * ((k : ℤ) + 1) * ((n : ℤ) - k) < 2 * ((n : ℤ) + 1)) :
    k = 0 ∨ k + 1 = n := by
  by_contra hne
  have hlow : 1 ≤ k := by omega
  have hhigh : k + 2 ≤ n := by omega
  have hpos : 0 ≤ ((k : ℤ) - 1) * ((n : ℤ) - k - 2) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

theorem A_triple_bound_rank {n k : ℕ} (hk : k < n)
    (h : 3 * ((k : ℤ) + 1) * ((n : ℤ) - k) < 2 * ((n : ℤ) + 1)) :
    n = 1 := by
  have hpos : 0 ≤ (k : ℤ) * ((n : ℤ) - k - 1) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

theorem leafExtension_B_cases {n : ℕ} (hn : 2 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.B n) k a b).IsFiniteCartan) (ha : a < 0) :
    a = -1 ∧ b = -1 ∧
      (k.val = 0 ∨ (n = 2 ∧ k.val = 1) ∨ (n = 3 ∧ k.val = 2)) := by
  have hp := leafExtension_B_bound hn hE ha.le
  have hpairs := leafExtension_negative_pairs hE ha
  have hk := k.isLt
  rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    split_ifs at hp <;> omega

theorem leafExtension_C_cases {n : ℕ} (hn : 2 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.C n) k a b).IsFiniteCartan) (ha : a < 0) :
    a = -1 ∧ b = -1 ∧
      (k.val = 0 ∨ (n = 2 ∧ k.val = 1) ∨ (n = 3 ∧ k.val = 2)) := by
  have hp := leafExtension_C_bound hn hE ha.le
  have hpairs := leafExtension_negative_pairs hE ha
  have hk := k.isLt
  rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    split_ifs at hp <;> omega

theorem leafExtension_D_cases {n : ℕ} (hn : 4 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.D n) k a b).IsFiniteCartan) (ha : a < 0) :
    a = -1 ∧ b = -1 ∧
      (k.val = 0 ∨ (n ≤ 7 ∧ (k.val + 1 = n ∨ k.val + 2 = n))) := by
  have hp := leafExtension_D_bound hn hE ha.le
  have hpairs := leafExtension_negative_pairs hE ha
  have hk := k.isLt
  rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    split_ifs at hp <;> omega

theorem leafExtension_A_exceptionalTypes {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (k : Fin n) (hk : k.val = 2 ∨ k.val + 3 = n) :
    HasIrreducibleCartanType (leafExtension (CartanMatrix.A n) k (-1) (-1)) := by
  interval_cases n <;> fin_cases k
  all_goals simp only at hk
  all_goals try omega
  · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 6)
      (Equiv.ofBijective (fun i : Fin 6 => ![(0 : Fin 6), 2, 3, 4, 5, 1] i)
        (by decide)) ?_).mpr hasType_E6
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 7)
      (Equiv.ofBijective (fun i : Fin 7 => ![(0 : Fin 7), 2, 3, 4, 5, 6, 1] i)
        (by decide)) ?_).mpr hasType_E7
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 7)
      (Equiv.ofBijective (fun i : Fin 7 => ![(6 : Fin 7), 5, 4, 3, 2, 0, 1] i)
        (by decide)) ?_).mpr hasType_E7
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 8)
      (Equiv.ofBijective (fun i : Fin 8 => ![(0 : Fin 8), 2, 3, 4, 5, 6, 7, 1] i)
        (by decide)) ?_).mpr hasType_E8
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 8)
      (Equiv.ofBijective (fun i : Fin 8 => ![(7 : Fin 8), 6, 5, 4, 3, 2, 0, 1] i)
        (by decide)) ?_).mpr hasType_E8
    intro i j
    fin_cases i <;> fin_cases j <;> decide

theorem leafExtension_A_simple_classification {n : ℕ} {k : Fin n}
    (hE : (leafExtension (CartanMatrix.A n) k (-1) (-1)).IsFiniteCartan) :
    HasIrreducibleCartanType (leafExtension (CartanMatrix.A n) k (-1) (-1)) := by
  have hbound := leafExtension_A_bound hE (by omega : (-1 : ℤ) ≤ 0)
  norm_num at hbound
  have hk := k.isLt
  by_cases hlast : k.val + 1 = n
  · rw [leafExtension_A_last_eq_A k hlast]
    exact hasType_A (by omega)
  by_cases hfirst : k.val = 0
  · apply (hasIrreducibleCartanType_congr _ (leafExtension_A_reflect k (-1) (-1))).mpr
    have hr : k.rev.val + 1 = n := by simp only [Fin.val_rev]; omega
    rw [leafExtension_A_last_eq_A k.rev hr]
    exact hasType_A (by omega)
  by_cases hpenult : k.val + 2 = n
  · rw [leafExtension_A_penultimate_eq_D (by omega) k hpenult]
    exact hasType_D (by omega)
  by_cases hsecond : k.val = 1
  · apply (hasIrreducibleCartanType_congr _ (leafExtension_A_reflect k (-1) (-1))).mpr
    have hr : k.rev.val + 2 = n := by simp only [Fin.val_rev]; omega
    rw [leafExtension_A_penultimate_eq_D (by omega) k.rev hr]
    exact hasType_D (by omega)
  have hcases := A_simple_bound_cases hk hbound
  apply leafExtension_A_exceptionalTypes (by omega) (by omega) k
  omega

theorem leafExtension_A_classification {n : ℕ} {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.A n) k a b).IsFiniteCartan) (ha : a < 0) :
    HasIrreducibleCartanType (leafExtension (CartanMatrix.A n) k a b) := by
  have hpairs := leafExtension_negative_pairs hE ha
  have hbound := leafExtension_A_bound hE ha.le
  have hk := k.isLt
  rcases hpairs with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact leafExtension_A_simple_classification hE
  · norm_num at hbound
    rcases A_double_bound_cases hk hbound with hfirst | hlast
    · apply (hasIrreducibleCartanType_congr _ (leafExtension_A_reflect k (-1) (-2))).mpr
      have hr : k.rev.val + 1 = n := by simp only [Fin.val_rev]; omega
      rw [leafExtension_A_last_eq_C k.rev hr]
      exact hasType_C (by omega)
    · rw [leafExtension_A_last_eq_C k hlast]
      exact hasType_C (by omega)
  · norm_num at hbound
    rcases A_double_bound_cases hk hbound with hfirst | hlast
    · apply (hasIrreducibleCartanType_congr _ (leafExtension_A_reflect k (-2) (-1))).mpr
      have hr : k.rev.val + 1 = n := by simp only [Fin.val_rev]; omega
      rw [leafExtension_A_last_eq_B k.rev hr]
      exact hasType_B (by omega)
    · rw [leafExtension_A_last_eq_B k hlast]
      exact hasType_B (by omega)
  · norm_num at hbound
    have hn := A_triple_bound_rank hk hbound
    subst n
    fin_cases k
    apply (hasIrreducibleCartanType_congr (N := CartanMatrix.G₂)
      Fin.revPerm ?_).mpr hasType_G2
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · norm_num at hbound
    have hn := A_triple_bound_rank hk hbound
    subst n
    fin_cases k
    apply (hasIrreducibleCartanType_congr (N := CartanMatrix.G₂)
      (Equiv.refl _) ?_).mpr hasType_G2
    intro i j
    fin_cases i <;> fin_cases j <;> decide

theorem leafExtension_B_classification {n : ℕ} (hn : 2 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.B n) k a b).IsFiniteCartan) (ha : a < 0) :
    HasIrreducibleCartanType (leafExtension (CartanMatrix.B n) k a b) := by
  obtain ⟨rfl, rfl, hcases⟩ := leafExtension_B_cases hn hE ha
  rcases hcases with hfirst | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact (hasIrreducibleCartanType_congr (finRotate (n + 1))
      (leafExtension_B_first_numbering hn k hfirst)).mpr (hasType_B (by omega))
  · have heq : k = 1 := Fin.ext hk
    subst k
    apply (hasIrreducibleCartanType_congr (N := CartanMatrix.C 3)
      Fin.revPerm ?_).mpr (hasType_C (by omega))
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · have heq : k = 2 := Fin.ext hk
    subst k
    apply (hasIrreducibleCartanType_congr (N := CartanMatrix.F₄)
      (Equiv.refl _) ?_).mpr hasType_F4
    intro i j
    fin_cases i <;> fin_cases j <;> decide

theorem leafExtension_C_classification {n : ℕ} (hn : 2 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.C n) k a b).IsFiniteCartan) (ha : a < 0) :
    HasIrreducibleCartanType (leafExtension (CartanMatrix.C n) k a b) := by
  obtain ⟨rfl, rfl, hcases⟩ := leafExtension_C_cases hn hE ha
  rcases hcases with hfirst | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact (hasIrreducibleCartanType_congr (finRotate (n + 1))
      (leafExtension_C_first_numbering hn k hfirst)).mpr (hasType_C (by omega))
  · have heq : k = 1 := Fin.ext hk
    subst k
    apply (hasIrreducibleCartanType_congr (N := CartanMatrix.B 3)
      Fin.revPerm ?_).mpr (hasType_B (by omega))
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  · have heq : k = 2 := Fin.ext hk
    subst k
    apply (hasIrreducibleCartanType_congr (N := CartanMatrix.F₄)
      Fin.revPerm ?_).mpr hasType_F4
    intro i j
    fin_cases i <;> fin_cases j <;> decide

theorem leafExtension_D_classification {n : ℕ} (hn : 4 ≤ n) {k : Fin n} {a b : ℤ}
    (hE : (leafExtension (CartanMatrix.D n) k a b).IsFiniteCartan) (ha : a < 0) :
    HasIrreducibleCartanType (leafExtension (CartanMatrix.D n) k a b) := by
  obtain ⟨rfl, rfl, hcases⟩ := leafExtension_D_cases hn hE ha
  rcases hcases with hfirst | ⟨hn7, hk⟩
  · exact (hasIrreducibleCartanType_congr (finRotate (n + 1))
      (leafExtension_D_first_numbering hn k hfirst)).mpr (hasType_D (by omega))
  · interval_cases n <;> fin_cases k
    all_goals simp only at hk
    all_goals try omega
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.D 5)
        (Equiv.ofBijective (fun i : Fin 5 => ![(3 : Fin 5), 2, 1, 4, 0] i)
          (by decide)) ?_).mpr (hasType_D (by omega))
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.D 5)
        (Equiv.ofBijective (fun i : Fin 5 => ![(3 : Fin 5), 2, 4, 1, 0] i)
          (by decide)) ?_).mpr (hasType_D (by omega))
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 6)
        (Equiv.ofBijective (fun i : Fin 6 => ![(0 : Fin 6), 2, 3, 4, 1, 5] i)
          (by decide)) ?_).mpr (hasType_E6)
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 6)
        (Equiv.ofBijective (fun i : Fin 6 => ![(0 : Fin 6), 2, 3, 1, 4, 5] i)
          (by decide)) ?_).mpr (hasType_E6)
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 7)
        (Equiv.ofBijective (fun i : Fin 7 => ![(6 : Fin 7), 5, 4, 3, 2, 1, 0] i)
          (by decide)) ?_).mpr (hasType_E7)
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 7)
        (Equiv.ofBijective (fun i : Fin 7 => ![(6 : Fin 7), 5, 4, 3, 1, 2, 0] i)
          (by decide)) ?_).mpr (hasType_E7)
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 8)
        (Equiv.ofBijective (fun i : Fin 8 => ![(7 : Fin 8), 6, 5, 4, 3, 2, 1, 0] i)
          (by decide)) ?_).mpr (hasType_E8)
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    · apply (hasIrreducibleCartanType_congr (N := CartanMatrix.E 8)
        (Equiv.ofBijective (fun i : Fin 8 => ![(7 : Fin 8), 6, 5, 4, 3, 1, 2, 0] i)
          (by decide)) ?_).mpr (hasType_E8)
      intro i j
      fin_cases i <;> fin_cases j <;> decide

end Langlands.LinearAlgebra.FiniteCartanMatrix
