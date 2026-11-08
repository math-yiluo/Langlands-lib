import Langlands.Representation.RankinSelberg.HighlyRamified.DualMatrix
import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Group.GL.LowerTriangularBlockCoordinates

/-!
# Level membership of dual matrices and the lower-block factorization

`M(u) = w ᵗdiag(u,1)⁻¹ w` lies in the level-`f` subgroup when `u` and `u⁻¹` are integral
and the first column of `u⁻¹` is congruent to `e_0` modulo `𝔭^f`. The lower-block
representative `[[g,0],[x,h]]` (one final row) factors as `diag(g,1) · [[I,0],[x,h]]`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {n : ℕ}

theorem rankInclusion_entry_mem_integer (u : GeneralLinearGroup (Fin (n + 1)) F)
    (hu : ∀ i j, u i j ∈ (ValuativeRel.valuation F).integer) (i j : Fin (n + 2)) :
    rankInclusion 1 u i j ∈ (ValuativeRel.valuation F).integer := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [Iwasawa.rankInclusion_castSucc_castSucc]; exact hu i' j'
  · rw [Iwasawa.rankInclusion_castSucc_last]; exact Subring.zero_mem _
  · rw [Iwasawa.rankInclusion_last_castSucc]; exact Subring.zero_mem _
  · rw [Iwasawa.rankInclusion_last_last]; exact Subring.one_mem _

/-- `M(u)` lies in the level-`f` subgroup when `u, u⁻¹` are integral and the first column of
`u⁻¹` is `e_0` modulo `𝔭^f`. -/
theorem dualConj_mem_levelSubgroup {f : ℕ} (u : GeneralLinearGroup (Fin (n + 1)) F)
    (hu : ∀ i j, u i j ∈ (ValuativeRel.valuation F).integer)
    (huinv : ∀ i j, (u⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) i j ∈
      (ValuativeRel.valuation F).integer)
    (hcol : ∀ k, ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = (u⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) k 0 -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) k 0) :
    dualConj u ∈ Conductor.levelSubgroup F (n + 1) f := by
  apply mem_levelSubgroup_of_entries
  · intro i j
    rw [dualConj_entry, ← map_inv]
    exact rankInclusion_entry_mem_integer _ huinv _ _
  · intro i j
    rw [dualConj_inv_entry]
    exact rankInclusion_entry_mem_integer _ hu _ _
  · intro j
    rw [dualConj_entry, ← map_inv, Fin.rev_last]
    have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
    rw [h0]
    rcases Fin.eq_castSucc_or_eq_last j.rev with ⟨k, hk⟩ | hk
    · rw [hk, Iwasawa.rankInclusion_castSucc_castSucc]
      obtain ⟨x, hx, hxe⟩ := hcol k
      refine ⟨x, hx, ?_⟩
      rw [hxe]
      congr 1
      have hj : j = k.castSucc.rev := by rw [← hk, Fin.rev_rev]
      by_cases hk0 : k = 0
      · subst hk0
        have : j = Fin.last (n + 1) := by rw [hj]; ext; simp
        rw [this, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hk0]
        have : Fin.last (n + 1) ≠ j := by
          intro h
          apply hk0
          rw [← h, Fin.rev_last] at hk
          exact Fin.castSucc_injective _ (by rw [← hk]; rfl)
        rw [Matrix.one_apply_ne this]
    · rw [hk, Iwasawa.rankInclusion_last_castSucc]
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have : Fin.last (n + 1) ≠ j := by
        intro h
        rw [← h, Fin.rev_last] at hk
        exact absurd (congrArg Fin.val hk) (by simp)
      rw [Matrix.one_apply_ne this]
      simp

section LowerBlock

variable {m : ℕ}

theorem natAdd_zero_eq_last : Fin.natAdd (m + 1) (0 : Fin 1) = Fin.last (m + 1) := by
  ext; simp

omit [ValuativeRel F] in
/-- `[[g,0],[x,h]] = diag(g,1) · [[I,0],[x,h]]`. -/
theorem lowerBlockPair_eq_rankInclusion_mul (g : GeneralLinearGroup (Fin (m + 1)) F)
    (x : Matrix (Fin 1) (Fin (m + 1)) F) (h : lowerTriangularSubgroup 1 F) :
    lowerBlockPair g x h = rankInclusion 1 g * lowerBlockPair 1 x h := by
  rw [rankInclusion_mul_lowerBlockPair, mul_one]

/-- `M([[I,0],[x,h]])` lies in the level-`f` subgroup when `x` is integral with
`x_(0,0) ∈ 𝔭^f` and `h` is an integral unit. -/
theorem dualConj_lowerBlockPair_one_mem {f : ℕ} (x : Matrix (Fin 1) (Fin (m + 1)) F)
    (h : lowerTriangularSubgroup 1 F)
    (hx : ∀ j, x 0 j ∈ (ValuativeRel.valuation F).integer)
    (hx0 : ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (y : F) = x 0 0)
    (hh : h.val 0 0 ∈ (ValuativeRel.valuation F).integer)
    (hhinv : (h.val⁻¹ : GeneralLinearGroup (Fin 1) F) 0 0 ∈ (ValuativeRel.valuation F).integer) :
    dualConj (lowerBlockPair 1 x h) ∈ Conductor.levelSubgroup F (m + 1 + 1) f := by
  have hentry : ∀ j, (-(h.val⁻¹ : GeneralLinearGroup (Fin 1) F).val * x *
      ((1 : GeneralLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) 0 j =
      -((h.val⁻¹ : GeneralLinearGroup (Fin 1) F) 0 0 * x 0 j) := by
    intro j
    simp [Matrix.mul_apply, Matrix.one_apply]
  apply dualConj_mem_levelSubgroup
  · intro i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [show (i'.castSucc : Fin (m + 1 + 1)) = i'.castAdd 1 from rfl,
        show (j'.castSucc : Fin (m + 1 + 1)) = j'.castAdd 1 from rfl, lowerBlockPair_11]
      by_cases hij : i' = j'
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    · rw [show (i'.castSucc : Fin (m + 1 + 1)) = i'.castAdd 1 from rfl, ← natAdd_zero_eq_last,
        lowerBlockPair_12]
      exact Subring.zero_mem _
    · rw [show (j'.castSucc : Fin (m + 1 + 1)) = j'.castAdd 1 from rfl, ← natAdd_zero_eq_last,
        lowerBlockPair_21]
      exact hx j'
    · rw [← natAdd_zero_eq_last, lowerBlockPair_22]
      exact hh
  · intro i j
    rw [lowerBlockPair_inv]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [show (i'.castSucc : Fin (m + 1 + 1)) = i'.castAdd 1 from rfl,
        show (j'.castSucc : Fin (m + 1 + 1)) = j'.castAdd 1 from rfl, lowerBlockPair_11, inv_one]
      by_cases hij : i' = j'
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    · rw [show (i'.castSucc : Fin (m + 1 + 1)) = i'.castAdd 1 from rfl, ← natAdd_zero_eq_last,
        lowerBlockPair_12]
      exact Subring.zero_mem _
    · rw [show (j'.castSucc : Fin (m + 1 + 1)) = j'.castAdd 1 from rfl, ← natAdd_zero_eq_last,
        lowerBlockPair_21, inv_one]
      rw [hentry]
      exact Subring.neg_mem _ (Subring.mul_mem _ hhinv (hx j'))
    · rw [← natAdd_zero_eq_last, lowerBlockPair_22]
      exact hhinv
  · intro k
    rw [lowerBlockPair_inv]
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [show (k'.castSucc : Fin (m + 1 + 1)) = k'.castAdd 1 from rfl,
        show (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castAdd 1 from rfl, lowerBlockPair_11,
        inv_one]
      by_cases hk : k' = 0
      · subst hk; simp
      · rw [GeneralLinearGroup.coe_one, Matrix.one_apply_ne hk,
          Matrix.one_apply_ne (fun he => hk (Fin.castAdd_injective _ _ he))]
        simp
    · obtain ⟨y, hy, hye⟩ := hx0
      refine ⟨-((⟨(h.val⁻¹ : GeneralLinearGroup (Fin 1) F) 0 0, hhinv⟩ :
        (ValuativeRel.valuation F).integer) * y), ?_, ?_⟩
      · exact neg_mem (Ideal.mul_mem_left _ _ hy)
      · rw [← natAdd_zero_eq_last, show (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castAdd 1
          from rfl, lowerBlockPair_21, inv_one]
        have hl : (Fin.natAdd (m + 1) (0 : Fin 1)) ≠ (0 : Fin (m + 1)).castAdd 1 := by
          rw [natAdd_zero_eq_last]
          exact (Fin.castSucc_lt_last 0).ne'
        rw [Matrix.one_apply_ne hl, sub_zero, hentry]
        push_cast
        rw [hye]

end LowerBlock

end Langlands.RankinSelberg.HighlyRamified
