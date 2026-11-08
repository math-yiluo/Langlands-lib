import Langlands.Representation.RankinSelberg.HighlyRamified.LastRowAgreement
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Group.GL.Maps

/-!
# First-row unipotent convolutions of Whittaker functions

The test vectors of Jacquet–Shalika 1985, §4.4, formula (4) (printed page 328), are
finite combinations `Σ_z Φ(z) ρ(n(z)) W₀` of right translates by the first-row
unipotent matrices `n(z) = [[1, z], [0, I]]`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear Langlands.Whittaker

universe uF uV

section Matrices

variable {F : Type uF} [Field F] {n : ℕ}

/-- The nilpotent matrix whose first row is `(0, z_0, …, z_n)`. -/
def firstRowNil (z : Fin (n + 1) → F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F :=
  fun i j => if i = 0 then Fin.cases 0 z j else 0

theorem firstRowNil_sq (z : Fin (n + 1) → F) : firstRowNil z * firstRowNil z = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [firstRowNil]
  · simp [firstRowNil, Fin.succ_ne_zero]

/-- The first-row unipotent matrix `n(z) = [[1, z], [0, I]]`. -/
def firstRowUnipotent (z : Fin (n + 1) → F) : GeneralLinearGroup (Fin (n + 2)) F where
  val := 1 + firstRowNil z
  inv := 1 - firstRowNil z
  val_inv := by simp [mul_sub, add_mul, firstRowNil_sq]
  inv_val := by simp [sub_mul, mul_add, firstRowNil_sq]

theorem firstRowUnipotent_apply (z : Fin (n + 1) → F) (i j : Fin (n + 2)) :
    firstRowUnipotent z i j = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i j +
      firstRowNil z i j := rfl

theorem firstRowUnipotent_inv_apply (z : Fin (n + 1) → F) (i j : Fin (n + 2)) :
    (firstRowUnipotent z)⁻¹ i j = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i j -
      firstRowNil z i j := rfl

theorem firstRowNil_add (z z' : Fin (n + 1) → F) :
    firstRowNil (z + z') = firstRowNil z + firstRowNil z' := by
  ext i j
  refine Fin.cases ?_ (fun j' => ?_) j <;> by_cases hi : i = 0 <;> simp [firstRowNil, hi]

theorem firstRowNil_mul (z z' : Fin (n + 1) → F) :
    firstRowNil z * firstRowNil z' = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp [firstRowNil]
  · simp [firstRowNil, Fin.succ_ne_zero]

theorem firstRowUnipotent_mul (z z' : Fin (n + 1) → F) :
    firstRowUnipotent z * firstRowUnipotent z' = firstRowUnipotent (z + z') := by
  apply Units.ext
  change (1 + firstRowNil z) * (1 + firstRowNil z') = 1 + firstRowNil (z + z')
  rw [firstRowNil_add, mul_add, add_mul, add_mul, firstRowNil_mul]
  simp [add_assoc]

/-- `n(z)` is upper unipotent. -/
theorem firstRowUnipotent_mem (z : Fin (n + 1) → F) :
    firstRowUnipotent z ∈ upperUnipotent (n + 2) F := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    rw [firstRowUnipotent_apply]
    have hne : i ≠ j := fun h => (lt_irrefl _ (h ▸ hij))
    have hi : i ≠ 0 := by
      intro h
      subst h
      exact absurd hij (not_lt.mpr (Fin.zero_le j))
    simp [Matrix.one_apply_ne hne, firstRowNil, hi]
  · rw [firstRowUnipotent_apply]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [firstRowNil]
    · simp [firstRowNil, Fin.succ_ne_zero]

/-- The superdiagonal sum of `n(z)` is `z_0`. -/
theorem firstRowUnipotent_superdiagonal (z : Fin (n + 1) → F) :
    ∑ i : Fin (n + 1), firstRowUnipotent z i.castSucc i.succ = z 0 := by
  rw [Fin.sum_univ_succ]
  have h0 : firstRowUnipotent z (0 : Fin (n + 1)).castSucc (0 : Fin (n + 1)).succ = z 0 := by
    rw [firstRowUnipotent_apply, Fin.castSucc_zero,
      Matrix.one_apply_ne (Fin.succ_ne_zero 0).symm]
    simp only [firstRowNil, zero_add]
    rfl
  have hrest : ∀ i : Fin n, firstRowUnipotent z i.castSucc.succ i.succ.succ = 0 := by
    intro i
    rw [firstRowUnipotent_apply]
    have hne : i.castSucc.succ ≠ i.succ.succ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hi : i.castSucc.succ ≠ 0 := Fin.succ_ne_zero _
    simp [Matrix.one_apply_ne hne, firstRowNil, hi]
  rw [h0]
  simp [hrest]

theorem inv_mul_self_matrix (M : GeneralLinearGroup (Fin (n + 2)) F) :
    ((M⁻¹ : GeneralLinearGroup (Fin (n + 2)) F) : Matrix (Fin (n + 2)) (Fin (n + 2)) F) *
      (M : Matrix (Fin (n + 2)) (Fin (n + 2)) F) = 1 := by
  rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]

/-- If `M` has first column equal to that of the identity, conjugation by
`M` maps `n(z)` to `n(z')` with `z'_j = Σ_k z_k M⁻¹_(k+1, j+1)`. -/
theorem mul_firstRowUnipotent (M : GeneralLinearGroup (Fin (n + 2)) F)
    (hcol : ∀ i, M i 0 = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i 0)
    (z : Fin (n + 1) → F) :
    M * firstRowUnipotent z =
      firstRowUnipotent (fun j => ∑ k, z k * (M⁻¹ : GeneralLinearGroup (Fin (n + 2)) F)
        k.succ j.succ) * M := by
  have hI := inv_mul_self_matrix M
  have hinvcol : ∀ i, (M⁻¹ : GeneralLinearGroup (Fin (n + 2)) F) i 0 =
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i 0 := by
    intro i
    have h := congrFun (congrFun hI i) 0
    rw [Matrix.mul_apply, Finset.sum_eq_single 0] at h
    · rw [← h, hcol 0]
      simp
    · intro k _ hk
      rw [hcol k, Matrix.one_apply_ne hk, mul_zero]
    · simp
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (M : Matrix (Fin (n + 2)) (Fin (n + 2)) F) * (1 + firstRowNil z) =
    (1 + firstRowNil _) * (M : Matrix (Fin (n + 2)) (Fin (n + 2)) F)
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (0 : Fin (n + 2))]
  rotate_left
  · intro k _ hk
    simp [firstRowNil, hk]
  · simp
  by_cases hi : i = 0
  · subst hi
    rw [hcol 0]
    simp only [Matrix.one_apply_eq, one_mul, firstRowNil, ite_true]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, zero_mul, zero_add, Fin.cases_succ]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have key : ∀ l : Fin (n + 1), ∑ k : Fin (n + 1), z l *
        (M⁻¹ : GeneralLinearGroup (Fin (n + 2)) F) l.succ k.succ * M k.succ j =
        z l * (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) l.succ j := by
      intro l
      have h := congrFun (congrFun hI l.succ) j
      rw [Matrix.mul_apply, Fin.sum_univ_succ, hinvcol l.succ,
        Matrix.one_apply_ne (Fin.succ_ne_zero l), zero_mul, zero_add] at h
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [h]
    simp_rw [key]
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp [Fin.succ_ne_zero]
    · simp only [Fin.cases_succ]
      rw [Finset.sum_eq_single j']
      · simp
      · intro l _ hl
        rw [Matrix.one_apply_ne (fun h => hl (Fin.succ_injective _ h)), mul_zero]
      · simp
  · rw [hcol i, Matrix.one_apply_ne hi, zero_mul]
    simp [firstRowNil, hi]

/-- The entries of `n(z)` in its first row. -/
theorem firstRowUnipotent_zero_apply (z : Fin (n + 1) → F) (j : Fin (n + 2)) :
    firstRowUnipotent z 0 j = Fin.cases 1 z j := by
  rw [firstRowUnipotent_apply]
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp [firstRowNil]
  · rw [Matrix.one_apply_ne (Fin.succ_ne_zero j').symm, zero_add]
    simp only [firstRowNil, ite_true]
    rfl

/-- The last row of `w · n(z)` is `(1, z_0, …, z_n)`. -/
theorem weylLong_mul_firstRowUnipotent_last (z : Fin (n + 1) → F) (j : Fin (n + 2)) :
    (weylLong (n + 2) F * firstRowUnipotent z) (Fin.last (n + 1)) j = Fin.cases 1 z j := by
  rw [weylLong_mul_entry, Fin.rev_last, firstRowUnipotent_zero_apply]

section Level

variable [ValuativeRel F]

/-- `n(z)` lies in every level subgroup when `z` is integral. -/
theorem firstRowUnipotent_mem_levelSubgroup {f : ℕ} (z : Fin (n + 1) → F)
    (hz : ∀ j, z j ∈ (ValuativeRel.valuation F).integer) :
    firstRowUnipotent z ∈ Conductor.levelSubgroup F (n + 1) f := by
  have hone : ∀ i j, (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i j ∈
      (ValuativeRel.valuation F).integer := fun i j => by
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hnil : ∀ i j, firstRowNil z i j ∈ (ValuativeRel.valuation F).integer := fun i j => by
    unfold firstRowNil
    split_ifs
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact Subring.zero_mem _
      · exact hz j'
    · exact Subring.zero_mem _
  apply mem_levelSubgroup_of_entries
  · intro i j
    exact Subring.add_mem _ (hone i j) (hnil i j)
  · intro i j
    exact Subring.sub_mem _ (hone i j) (hnil i j)
  · intro j
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [firstRowUnipotent_apply]
    have hl : Fin.last (n + 1) ≠ 0 := Fin.last_pos.ne'
    simp [firstRowNil, hl]

end Level

end Matrices

section Whittaker

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- A standard Whittaker function at `M n(z)`, for `M` with standard first column. -/
theorem whittaker_mul_firstRowUnipotent (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ (n + 1)) (M : GeneralLinearGroup (Fin (n + 2)) F)
    (hcol : ∀ i, M i 0 = (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i 0)
    (z : Fin (n + 1) → F) :
    W.val (M * firstRowUnipotent z) =
      ψ.complex (∑ k, z k * (M⁻¹ : GeneralLinearGroup (Fin (n + 2)) F) k.succ 1) *
        W.val M := by
  rw [mul_firstRowUnipotent M hcol z]
  set z' : Fin (n + 1) → F := fun j => ∑ k, z k * (M⁻¹ : GeneralLinearGroup (Fin (n + 2)) F)
    k.succ j.succ with hz'
  have h := W.property (⟨firstRowUnipotent z', firstRowUnipotent_mem z'⟩ :
    upperUnipotent (n + 2) F) M
  change W.val (firstRowUnipotent z' * M) = _
  rw [h, standardCharacter_apply]
  congr 2
  exact firstRowUnipotent_superdiagonal z'

end Whittaker

end Langlands.RankinSelberg.HighlyRamified
