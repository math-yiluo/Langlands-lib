import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Monoid.WithTop

/-! # Unshifted coordinate depths for the SU3 root parameter group -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

/-- Halving a real valuation value, with infinity preserved. -/
def halfTop : WithTop ℝ → WithTop ℝ := WithTop.map (fun t : ℝ => t / 2)

/-- Doubling a real valuation value, with infinity preserved. -/
def doubleTop : WithTop ℝ → WithTop ℝ := WithTop.map (fun t : ℝ => 2 * t)

@[simp] theorem halfTop_top : halfTop ⊤ = ⊤ := rfl
@[simp] theorem halfTop_coe (t : ℝ) : halfTop t = (↑(t / 2) : WithTop ℝ) := rfl
@[simp] theorem doubleTop_top : doubleTop ⊤ = ⊤ := rfl
@[simp] theorem doubleTop_coe (t : ℝ) : doubleTop t = (↑(2 * t) : WithTop ℝ) := rfl

@[simp] theorem halfTop_eq_top_iff (t : WithTop ℝ) : halfTop t = ⊤ ↔ t = ⊤ := by
  simp [halfTop]

@[simp] theorem doubleTop_halfTop (t : WithTop ℝ) : doubleTop (halfTop t) = t := by
  cases t using WithTop.recTopCoe with
  | top => rfl
  | coe t => rw [halfTop_coe, doubleTop_coe]; congr 1; ring

@[simp] theorem halfTop_doubleTop (t : WithTop ℝ) : halfTop (doubleTop t) = t := by
  cases t using WithTop.recTopCoe with
  | top => rfl
  | coe t => rw [doubleTop_coe, halfTop_coe]; congr 1; ring

/-- A direct threshold comparison, including the infinite value. -/
theorem coe_le_halfTop_iff (r : ℝ) (t : WithTop ℝ) :
    (r : WithTop ℝ) ≤ halfTop t ↔ (↑(2 * r) : WithTop ℝ) ≤ t := by
  cases t using WithTop.recTopCoe with
  | top => simp
  | coe t => simp only [halfTop_coe, WithTop.coe_le_coe]; constructor <;> intro h <;> linarith

/-- Cancel doubling in a finite lower-bound comparison. -/
theorem coe_double_le_add_self_iff (r : ℝ) (t : WithTop ℝ) :
    (↑(2 * r) : WithTop ℝ) ≤ t + t ↔ (r : WithTop ℝ) ≤ t := by
  cases t using WithTop.recTopCoe with
  | top => simp
  | coe t => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]; constructor <;> intro h <;> linarith

/-- Every extended real value has a finite real lower bound. -/
theorem exists_real_le (t : WithTop ℝ) : ∃ r : ℝ, (r : WithTop ℝ) ≤ t := by
  cases t using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

/-- An extended real value above every real number is infinity. -/
theorem forall_real_le_iff (t : WithTop ℝ) :
    (∀ r : ℝ, (r : WithTop ℝ) ≤ t) ↔ t = ⊤ := by
  cases t using WithTop.recTopCoe with
  | top => simp
  | coe t =>
    simp only [WithTop.coe_le_coe, WithTop.coe_ne_top, iff_false]
    intro h
    have := h (t + 1)
    linarith

universe u v
variable {L : Type u} {M : Type v} [Field L] [Field M]

namespace Parameters
variable {c : RingInvolution L} {d : RingInvolution M}

/-- The unshifted depth for the multipliable root. -/
def depthA (omega : AddValuation L (WithTop ℝ)) (x : Parameters c) : WithTop ℝ :=
  halfTop (omega x.second)

/-- The unshifted depth on the literal zero-first-coordinate subgroup. -/
def depthDouble (omega : AddValuation L (WithTop ℝ)) (z : central c) : WithTop ℝ :=
  omega z.val.second

/-- Over a field the second coordinate vanishes only at the identity. -/
@[simp] theorem second_eq_zero_iff (x : Parameters c) : x.second = 0 ↔ x = 1 := by
  constructor
  · intro hv
    apply ext
    · have hu : x.first * c.bar x.first = 0 := by rw [← equation, hv]; simp
      rcases mul_eq_zero.mp hu with h | h
      · exact h
      · simpa using congrArg c.bar h
    · exact hv
  · rintro rfl
    rfl

@[simp] theorem depthA_eq_top_iff (omega : AddValuation L (WithTop ℝ)) (x : Parameters c) :
    depthA omega x = ⊤ ↔ x = 1 := by
  simp [depthA]

@[simp] theorem depthDouble_eq_top_iff (omega : AddValuation L (WithTop ℝ)) (z : central c) :
    depthDouble omega z = ⊤ ↔ z = 1 := by
  simp only [depthDouble, AddValuation.top_iff, second_eq_zero_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Doubling on the central subgroup uses the literal inclusion into the parameter group. -/
theorem depthDouble_eq_double_depthA (omega : AddValuation L (WithTop ℝ)) (z : central c) :
    depthDouble omega z = doubleTop (depthA omega z.val) := by
  simp [depthDouble, depthA]

variable (omega : AddValuation L (WithTop ℝ))
  (hinv : ∀ z : L, omega (c.bar z) = omega z)

include hinv in
@[simp] theorem depthA_inv (x : Parameters c) : depthA omega x⁻¹ = depthA omega x := by
  simp only [depthA, second_inv, hinv]

include hinv in
@[simp] theorem depthDouble_inv (z : central c) :
    depthDouble omega z⁻¹ = depthDouble omega z := by
  change omega (z.val⁻¹).second = omega z.val.second
  rw [second_inv, hinv]

include hinv in
/-- The trace-norm relation supplies the bound needed for product closure. -/
theorem second_le_first_add_first (x : Parameters c) :
    omega x.second ≤ omega x.first + omega x.first := by
  have h := omega.map_add x.second (c.bar x.second)
  rw [hinv, min_self, equation, omega.map_mul, hinv] at h
  exact h

include hinv in
/-- A second-coordinate threshold implies the first-coordinate threshold. -/
theorem first_ge_of_second_ge (r : ℝ) (x : Parameters c)
    (hx : (↑(2 * r) : WithTop ℝ) ≤ omega x.second) :
    (r : WithTop ℝ) ≤ omega x.first :=
  (coe_double_le_add_self_iff r (omega x.first)).mp
    (hx.trans (second_le_first_add_first omega hinv x))

/-- A coordinate map preserves depth when it preserves the supplied valuation. -/
theorem depthA_map (omega' : AddValuation M (WithTop ℝ)) (f : L →+* M)
    (hf : ∀ z, f (c.bar z) = d.bar (f z))
    (hval : ∀ z, omega' (f z) = omega z) (x : Parameters c) :
    depthA omega' (map f hf x) = depthA omega x := by
  simp only [depthA, second_map, hval]

/-- The induced homomorphism on the actual central subgroups. -/
def centralMap (f : L →+* M) (hf : ∀ z, f (c.bar z) = d.bar (f z)) :
    central c →* central d where
  toFun z := ⟨map f hf z.val, by simp only [mem_central, first_map]; rw [(mem_central z.val).mp z.property]; exact map_zero f⟩
  map_one' := Subtype.ext ((map f hf).map_one)
  map_mul' x y := Subtype.ext ((map f hf).map_mul x.val y.val)

@[simp] theorem centralMap_val (f : L →+* M) (hf : ∀ z, f (c.bar z) = d.bar (f z))
    (z : central c) : (centralMap f hf z).val = map f hf z.val := rfl

/-- Central depth is preserved by the induced central map. -/
theorem depthDouble_map (omega' : AddValuation M (WithTop ℝ)) (f : L →+* M)
    (hf : ∀ z, f (c.bar z) = d.bar (f z))
    (hval : ∀ z, omega' (f z) = omega z) (z : central c) :
    depthDouble omega' (centralMap f hf z) = depthDouble omega z := by
  exact hval z.val.second

end Parameters
end Langlands.GroupScheme.SU3Root
