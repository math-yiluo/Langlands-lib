import Langlands.Representation.Exponents.PositiveRootParameterConeStatement

/-! # Strict cone comparison in the actual flattened coordinates -/

noncomputable section

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeRegularComparison
open scoped BigOperators

namespace PositiveRootParameterConeProof

private theorem reindex_roots {r : ℕ} (c : ℕ → ℝ) (k : Fin r) :
    (∑ m ∈ Finset.Ioo 0 r, c m • simpleRoot r m) k =
      ∑ j : Fin (r - 1), c (j.val + 1) *
        ((if k.val = j.val then (1 : ℝ) else 0) -
          (if k.val = j.val + 1 then (1 : ℝ) else 0)) := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_bij
    (fun m hm => (⟨m - 1, by
      have := Finset.mem_Ioo.mp hm
      omega⟩ : Fin (r - 1))) ?_ ?_ ?_ ?_
  · intro m hm
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have ha' := Finset.mem_Ioo.mp ha
    have hb' := Finset.mem_Ioo.mp hb
    have h := congrArg Fin.val hab
    dsimp at h
    omega
  · intro j hj
    refine ⟨j.val + 1, Finset.mem_Ioo.mpr ⟨by omega, by have := j.isLt; omega⟩, ?_⟩
    apply Fin.ext
    simp
  · intro m hm
    have hm' := Finset.mem_Ioo.mp hm
    have hsub : m - 1 + 1 = m := by omega
    simp only [hsub, simpleRoot]
    congr 1
    split_ifs <;> first | (exfalso; omega) | ring

private theorem cone_iff_adjacent {r : ℕ} (x : Fin r → ℝ) :
    IsPositiveRootCone x ↔
      ∃ c : Fin (r - 1) → ℝ, (∀ j, 0 < c j) ∧
        ∀ k : Fin r, x k = ∑ j : Fin (r - 1), c j *
          ((if k.val = j.val then (1 : ℝ) else 0) -
            (if k.val = j.val + 1 then (1 : ℝ) else 0)) := by
  classical
  constructor
  · intro hx
    obtain ⟨c, hc, hexp⟩ := (isPositiveRootCone_iff_exists_simpleRoot x).mp hx
    refine ⟨fun j => c (j.val + 1), ?_, ?_⟩
    · intro j
      exact hc (j.val + 1) (by omega) (by have := j.isLt; omega)
    · intro k
      rw [hexp]
      exact reindex_roots c k
  · rintro ⟨c, hc, hexp⟩
    let d : ℕ → ℝ := fun m =>
      if hm : m - 1 < r - 1 then c ⟨m - 1, hm⟩ else 0
    have hd (j : Fin (r - 1)) : d (j.val + 1) = c j := by
      simp [d]
    apply (isPositiveRootCone_iff_exists_simpleRoot x).mpr
    refine ⟨d, ?_, funext fun k => ?_⟩
    · intro m hm hmr
      have h : m - 1 < r - 1 := by omega
      simpa only [d, dite_eq_left h] using hc ⟨m - 1, h⟩
    · rw [hexp k, reindex_roots]
      simp_rw [hd]

private theorem size_cancel (d c : ℝ) (hd : d ≠ 0)
    (P Q : Prop) [Decidable P] [Decidable Q] :
    d * (c * ((if P then (1 : ℝ) / d else 0) -
      (if Q then (1 : ℝ) / d else 0))) =
      c * ((if P then (1 : ℝ) else 0) - (if Q then (1 : ℝ) else 0)) := by
  split_ifs <;> field_simp [hd] <;> ring

theorem parameter_iff_cone {n : ℕ} (D : BlockShape n) (R : BlockRefinement D)
    (v : Fin (D.flatten R).length → ℝ) :
    IsPositiveRootParameter D R v ↔
      ∀ i : Fin D.length, IsPositiveRootCone (fun k : Fin (R i).length =>
        ((R i).size k : ℝ) * v (D.flattenBlockEquiv R ⟨i, k⟩)) := by
  classical
  constructor
  · rintro ⟨c, hc, hexp⟩ i
    apply (cone_iff_adjacent _).mpr
    refine ⟨c i, hc i, fun k => ?_⟩
    rw [hexp i k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact size_cancel _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ((R i).positive k))) _ _
  · intro hv
    choose c hc hexp using fun i => (cone_iff_adjacent _).mp (hv i)
    refine ⟨c, hc, fun i k => ?_⟩
    have hd : ((R i).size k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt ((R i).positive k))
    apply mul_left_cancel₀ hd
    rw [hexp i k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (size_cancel _ _ hd _ _).symm

end PositiveRootParameterConeProof

/-- Exact comparison of the scalar-root expansion and strict weighted prefix cone. -/
theorem positiveRootParameterCone : PositiveRootParameterConeStatement :=
  fun _ D R v => PositiveRootParameterConeProof.parameter_iff_cone D R v

end Langlands.Exponents
