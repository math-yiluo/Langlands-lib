import Langlands.Representation.Aubert.SignedCutComplex
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range

/-! Comparison of right and left exterior insertion on actual cut diagrams. -/

noncomputable section

namespace Langlands.Aubert.CutComplex

open scoped BigOperators

universe uI uM

variable {ι : Type uI} [LinearOrder ι]

/-- The number of target cuts to the right of the inserted cut. -/
def rightPosition (s : Finset ι) (i : ι) : ℕ := (s.filter (i < ·)).card

/-- The sign obtained by appending a cut on the right and sorting increasingly. -/
def rightSign (s : Finset ι) (i : ι) : ℂ := (-1 : ℂ) ^ rightPosition s i

/-- The two insertion positions partition all cuts other than the inserted one. -/
theorem position_add_rightPosition {s : Finset ι} {i : ι} (hi : i ∈ s) :
    position s i + rightPosition s i + 1 = s.card := by
  have hleft : (s.erase i).filter (· < i) = s.filter (· < i) := by
    simp [Finset.filter_erase]
  have hright : (s.erase i).filter (fun a => ¬ a < i) = s.filter (i < ·) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, ha⟩, hle⟩
      exact ⟨ha, lt_of_le_of_ne (le_of_not_gt hle) (Ne.symm hne)⟩
    · rintro ⟨ha, hlt⟩
      exact ⟨⟨ne_of_gt hlt, ha⟩, not_lt_of_ge hlt.le⟩
  have hcount := Finset.card_filter_add_card_filter_not (s := s.erase i) (· < i)
  rw [hleft, hright] at hcount
  exact (congrArg (· + 1) hcount).trans (Finset.card_erase_add_one hi)

/-- On a target with `k + 1` cuts, right insertion is `(-1)^k` times left insertion. -/
theorem rightSign_eq_degree_sign {s : Finset ι} {i : ι} (hi : i ∈ s)
    {k : ℕ} (hs : s.card = k + 1) :
    rightSign s i = (-1 : ℂ) ^ k * sign s i := by
  have hcount : position s i + rightPosition s i = k := by
    have := position_add_rightPosition hi
    omega
  have hsquare : ((-1 : ℂ) ^ position s i) * ((-1 : ℂ) ^ position s i) = 1 := by
    rw [← mul_pow]
    simp
  rw [← hcount, pow_add, sign, rightSign]
  calc
    (-1 : ℂ) ^ rightPosition s i =
        1 * (-1 : ℂ) ^ rightPosition s i := (one_mul _).symm
    _ = (((-1 : ℂ) ^ position s i) * ((-1 : ℂ) ^ position s i)) *
        (-1 : ℂ) ^ rightPosition s i := by rw [hsquare]
    _ = _ := by ring

/-- The scalar that changes the degreewise orientation of an increasing basis. -/
def degreeOrientation (k : ℕ) : ℂ := (-1 : ℂ) ^ k.choose 2

theorem degreeOrientation_eq_triangle (k : ℕ) :
    degreeOrientation k = (-1 : ℂ) ^ (k * (k - 1) / 2) := by
  rw [degreeOrientation, Nat.choose_two_right]

theorem degreeOrientation_succ (k : ℕ) :
    degreeOrientation (k + 1) = (-1 : ℂ) ^ k * degreeOrientation k := by
  rw [degreeOrientation, Nat.choose_succ_succ' k 1, Nat.choose_one_right,
    pow_add, degreeOrientation]

@[simp]
theorem degreeOrientation_square (k : ℕ) :
    degreeOrientation k * degreeOrientation k = 1 := by
  simp [degreeOrientation, ← mul_pow]

namespace Diagram

variable (D : Diagram.{uI,uM} ι)

/-- Right exterior insertion, with the unchanged diagram map. -/
def rightStep (i : ι) : D.Total →ₗ[ℂ] D.Total where
  toFun x s :=
    if i ∈ s then rightSign s i • D.map (Finset.erase_subset i s) (x (s.erase i)) else 0
  map_add' x y := by
    funext s
    by_cases hi : i ∈ s <;> simp [hi, map_add, smul_add]
  map_smul' a x := by
    funext s
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, Pi.smul_apply, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _
    · simp [hi]

@[simp]
theorem rightStep_apply (i : ι) (x : D.Total) (s : Finset ι) :
    D.rightStep i x s =
      if i ∈ s then rightSign s i • D.map (Finset.erase_subset i s) (x (s.erase i))
      else 0 := rfl

/-- The sign comparison holds on each actual insertion applied to a homogeneous family. -/
theorem rightStep_extend (i : ι) (k : ℕ) (x : D.Degree k) :
    D.rightStep i (D.extend k x) = (-1 : ℂ) ^ k • D.step i (D.extend k x) := by
  funext s
  by_cases hi : i ∈ s
  · by_cases hs : (s.erase i).card = k
    · have hcard : s.card = k + 1 := by
        rw [← hs, Finset.card_erase_add_one hi]
      simp only [rightStep_apply, step_apply, hi, ↓reduceIte, Pi.smul_apply]
      rw [rightSign_eq_degree_sign hi hcard, mul_smul]
    · simp only [rightStep_apply, step_apply, hi, ↓reduceIte, Pi.smul_apply,
        extend_apply, dite_eq_right hs, map_zero, smul_zero]
  · simp [hi]

/-- Scaling a homogeneous carrier by its orientation sign is an involutive equivalence. -/
def degreeOrientationEquiv (k : ℕ) : D.Degree k ≃ₗ[ℂ] D.Degree k where
  toFun x := degreeOrientation k • x
  invFun x := degreeOrientation k • x
  left_inv x := by
    change degreeOrientation k • (degreeOrientation k • x) = x
    rw [smul_smul, degreeOrientation_square, one_smul]
  right_inv x := by
    change degreeOrientation k • (degreeOrientation k • x) = x
    rw [smul_smul, degreeOrientation_square, one_smul]
  map_add' x y := smul_add _ _ _
  map_smul' a x := smul_comm _ _ _

@[simp]
theorem degreeOrientationEquiv_apply (k : ℕ) (x : D.Degree k) :
    D.degreeOrientationEquiv k x = degreeOrientation k • x := rfl

variable [Fintype ι]

/-- The differential using right exterior insertion. -/
def rightDifferential : D.Total →ₗ[ℂ] D.Total := ∑ i, D.rightStep i

theorem rightDifferential_extend (k : ℕ) (x : D.Degree k) :
    D.rightDifferential (D.extend k x) =
      (-1 : ℂ) ^ k • D.differential (D.extend k x) := by
  simp only [rightDifferential, LinearMap.sum_apply, rightStep_extend,
    differential_apply, Finset.smul_sum]

/-- The homogeneous differential obtained from actual right exterior insertions. -/
def rightDegreeDifferential (k : ℕ) : D.Degree k →ₗ[ℂ] D.Degree (k + 1) :=
  D.restrict (k + 1) ∘ₗ D.rightDifferential ∘ₗ D.extend k

/-- The two homogeneous differentials differ only by the source degree sign. -/
theorem rightDegreeDifferential_eq (k : ℕ) :
    D.rightDegreeDifferential k = (-1 : ℂ) ^ k • D.degreeDifferential k := by
  ext x
  simp only [rightDegreeDifferential, LinearMap.comp_apply, rightDifferential_extend,
    map_smul, degreeDifferential, LinearMap.smul_apply]

/-- The orientation equivalences carry the existing differential to right insertion. -/
theorem degreeOrientationEquiv_commutes (k : ℕ) (x : D.Degree k) :
    D.degreeOrientationEquiv (k + 1) (D.degreeDifferential k x) =
      D.rightDegreeDifferential k (D.degreeOrientationEquiv k x) := by
  simp only [degreeOrientationEquiv_apply, rightDegreeDifferential_eq,
    LinearMap.smul_apply, map_smul, smul_smul, degreeOrientation_succ, mul_comm]

theorem rightDegreeDifferential_square (k : ℕ) (x : D.Degree k) :
    D.rightDegreeDifferential (k + 1) (D.rightDegreeDifferential k x) = 0 := by
  simp only [rightDegreeDifferential_eq, LinearMap.smul_apply, map_smul,
    degreeDifferential_square, smul_zero]

/-- Reorientation preserves each actual homogeneous kernel. -/
theorem rightDegreeDifferential_ker (k : ℕ) :
    LinearMap.ker (D.rightDegreeDifferential k) =
      LinearMap.ker (D.degreeDifferential k) := by
  rw [rightDegreeDifferential_eq]
  exact LinearMap.ker_smul _ _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Reorientation preserves each actual homogeneous image. -/
theorem rightDegreeDifferential_range (k : ℕ) :
    LinearMap.range (D.rightDegreeDifferential k) =
      LinearMap.range (D.degreeDifferential k) := by
  rw [rightDegreeDifferential_eq]
  exact LinearMap.range_smul _ _ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

theorem rightDegreeDifferential_injective_iff (k : ℕ) :
    Function.Injective (D.rightDegreeDifferential k) ↔
      Function.Injective (D.degreeDifferential k) := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, rightDegreeDifferential_ker]

/-- Exactness of the actual homogeneous maps is independent of the insertion convention. -/
theorem rightDegreeDifferential_exact_iff (k : ℕ) :
    LinearMap.range (D.rightDegreeDifferential k) =
        LinearMap.ker (D.rightDegreeDifferential (k + 1)) ↔
      LinearMap.range (D.degreeDifferential k) =
        LinearMap.ker (D.degreeDifferential (k + 1)) := by
  rw [rightDegreeDifferential_range, rightDegreeDifferential_ker]

end Diagram
end Langlands.Aubert.CutComplex
