import Langlands.Group.GL.UpperUnipotent

/-!
# The upper-column unipotent for unequal-rank JPSS smearing

The leading block has rank `n + 1`, the rectangular block has `j + 1` rows,
and the smearing column is the following coordinate `n + j + 2`.
-/

noncomputable section

namespace Langlands.RankinSelberg

universe uF

variable {F : Type uF} [Field F]

/-- The upper column supported in the first `n + 1` rows and column `n + j + 2`. -/
def unequalRankSmearingEntries (n j k : ℕ) (z : Fin (n + 1) → F) :
    Matrix (Fin (n + ((j + 1) + k + 1) + 1))
      (Fin (n + ((j + 1) + k + 1) + 1)) F :=
  fun a b =>
    if ha : a.val < n + 1 then
      if b.val = n + j + 2 then z ⟨a.val, ha⟩ else 0
    else 0

/-- Any two such upper columns have zero product. -/
theorem unequalRankSmearingEntries_mul (n j k : ℕ)
    (z z' : Fin (n + 1) → F) :
    unequalRankSmearingEntries n j k z * unequalRankSmearingEntries n j k z' = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c.val < n + 1
  · have hc' : c.val ≠ n + j + 2 := by omega
    simp [unequalRankSmearingEntries, hc, hc']
  · simp [unequalRankSmearingEntries, hc]

/-- Square-zero identity used to construct the inverse. -/
theorem unequalRankSmearingEntries_sq (n j k : ℕ) (z : Fin (n + 1) → F) :
    unequalRankSmearingEntries n j k z * unequalRankSmearingEntries n j k z = 0 :=
  unequalRankSmearingEntries_mul n j k z z

@[simp] theorem unequalRankSmearingEntries_zero (n j k : ℕ) :
    unequalRankSmearingEntries (F := F) n j k 0 = 0 := by
  ext a b
  simp [unequalRankSmearingEntries]

/-- The supported column is additive in its vector. -/
theorem unequalRankSmearingEntries_add (n j k : ℕ) (z z' : Fin (n + 1) → F) :
    unequalRankSmearingEntries n j k (z + z') =
      unequalRankSmearingEntries n j k z + unequalRankSmearingEntries n j k z' := by
  ext a b
  simp only [unequalRankSmearingEntries, Matrix.add_apply]
  split <;> simp_all
  split <;> simp

/-- All entries on or below the diagonal vanish. -/
theorem unequalRankSmearingEntries_eq_zero_of_le (n j k : ℕ)
    (z : Fin (n + 1) → F)
    {a b : Fin (n + ((j + 1) + k + 1) + 1)} (h : b ≤ a) :
    unequalRankSmearingEntries n j k z a b = 0 := by
  by_cases ha : a.val < n + 1
  · have hb : b.val ≠ n + j + 2 := by
      simp only [Fin.le_def] at h
      omega
    simp [unequalRankSmearingEntries, ha, hb]
  · simp [unequalRankSmearingEntries, ha]

/-- The actual smearing matrix `I + E(z)`, with explicit inverse `I - E(z)`. -/
def unequalRankSmearingUnipotent (n j k : ℕ) (z : Fin (n + 1) → F) :
    Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F where
  val := 1 + unequalRankSmearingEntries n j k z
  inv := 1 - unequalRankSmearingEntries n j k z
  val_inv := by simp [mul_sub, add_mul, unequalRankSmearingEntries_sq]
  inv_val := by simp [sub_mul, mul_add, unequalRankSmearingEntries_sq]

@[simp] theorem unequalRankSmearingUnipotent_val (n j k : ℕ)
    (z : Fin (n + 1) → F) :
    (unequalRankSmearingUnipotent n j k z).val =
      1 + unequalRankSmearingEntries n j k z := rfl

/-- The inverse as an actual matrix. -/
@[simp] theorem unequalRankSmearingUnipotent_inv_val (n j k : ℕ)
    (z : Fin (n + 1) → F) :
    ((unequalRankSmearingUnipotent n j k z)⁻¹).val =
      1 - unequalRankSmearingEntries n j k z := rfl

/-- Entry formula in the same zero-based coordinates as `unequalRankMatrix`. -/
theorem unequalRankSmearingUnipotent_apply (n j k : ℕ)
    (z : Fin (n + 1) → F)
    (a b : Fin (n + ((j + 1) + k + 1) + 1)) :
    unequalRankSmearingUnipotent n j k z a b =
      (if a = b then 1 else 0) +
        if ha : a.val < n + 1 then
          if b.val = n + j + 2 then z ⟨a.val, ha⟩ else 0
        else 0 := by
  simp [unequalRankSmearingUnipotent, Matrix.one_apply, unequalRankSmearingEntries]

@[simp] theorem unequalRankSmearingUnipotent_zero (n j k : ℕ) :
    unequalRankSmearingUnipotent (F := F) n j k 0 = 1 := by
  apply Units.ext
  simp

/-- Vector addition becomes matrix multiplication. -/
theorem unequalRankSmearingUnipotent_add (n j k : ℕ) (z z' : Fin (n + 1) → F) :
    unequalRankSmearingUnipotent n j k (z + z') =
      unequalRankSmearingUnipotent n j k z * unequalRankSmearingUnipotent n j k z' := by
  apply Units.ext
  change 1 + unequalRankSmearingEntries n j k (z + z') =
    (1 + unequalRankSmearingEntries n j k z) * (1 + unequalRankSmearingEntries n j k z')
  simp only [unequalRankSmearingEntries_add, add_mul, mul_add, one_mul,
    mul_one, unequalRankSmearingEntries_mul, add_zero]
  ac_rfl

/-- The matrix belongs to the actual upper-unipotent subgroup. -/
theorem unequalRankSmearingUnipotent_mem_upperUnipotent (n j k : ℕ)
    (z : Fin (n + 1) → F) :
    unequalRankSmearingUnipotent n j k z ∈
      Langlands.GeneralLinear.upperUnipotent (n + ((j + 1) + k + 1) + 1) F := by
  constructor
  · intro a b hab
    change b < a at hab
    change (1 + unequalRankSmearingEntries n j k z) a b = 0
    simp only [Matrix.add_apply, Matrix.one_apply, ite_eq_right (ne_of_gt hab),
      unequalRankSmearingEntries_eq_zero_of_le n j k z (le_of_lt hab), add_zero]
  · intro a
    change (1 + unequalRankSmearingEntries n j k z) a a = 1
    simp [unequalRankSmearingEntries_eq_zero_of_le n j k z le_rfl]

section Topology

variable [TopologicalSpace F]

/-- Continuity of the supported column for the supplied topology. -/
theorem continuous_unequalRankSmearingEntries (n j k : ℕ) :
    Continuous (unequalRankSmearingEntries (F := F) n j k) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases ha : a.val < n + 1
  · by_cases hb : b.val = n + j + 2
    · simpa only [unequalRankSmearingEntries, dite_eq_left ha, ite_eq_left hb] using
        (continuous_apply (⟨a.val, ha⟩ : Fin (n + 1)) :
          Continuous fun z : Fin (n + 1) → F => z ⟨a.val, ha⟩)
    · simpa only [unequalRankSmearingEntries, dite_eq_left ha, ite_eq_right hb] using
        (continuous_const : Continuous fun _ : Fin (n + 1) → F => (0 : F))
  · simpa only [unequalRankSmearingEntries, dite_eq_right ha] using
      (continuous_const : Continuous fun _ : Fin (n + 1) → F => (0 : F))

variable [IsTopologicalRing F]

/-- Continuity into `GL` checks both the value and its explicit inverse. -/
theorem continuous_unequalRankSmearingUnipotent (n j k : ℕ) :
    Continuous (unequalRankSmearingUnipotent (F := F) n j k) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous fun z : Fin (n + 1) → F =>
      (1 : Matrix _ _ F) + unequalRankSmearingEntries n j k z
    exact continuous_const.add (continuous_unequalRankSmearingEntries n j k)
  · change Continuous fun z : Fin (n + 1) → F =>
      (1 : Matrix _ _ F) - unequalRankSmearingEntries n j k z
    exact continuous_const.sub (continuous_unequalRankSmearingEntries n j k)

end Topology

end Langlands.RankinSelberg
