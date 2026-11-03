import Langlands.Group.RelativeWeylIndexing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Inversion of the intrinsic relative-Weyl indexing and normalizer sections -/

namespace Langlands.Group.RelativeWeylIndexing

universe uB uW uA

variable {B : Type uB} {W : Type uW} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

theorem inv_mem_doubleCoset {I J : Finset B} {w x : W}
    (hx : x ∈ doubleCoset cs I J w) :
    x⁻¹ ∈ doubleCoset cs J I w⁻¹ := by
  rcases hx with ⟨a, ha, b, hb, rfl⟩
  exact ⟨b⁻¹, (standardSubgroup cs J).inv_mem hb,
    a⁻¹, (standardSubgroup cs I).inv_mem ha, by simp [mul_assoc]⟩

@[simp]
theorem inv_mem_doubleCoset_iff (I J : Finset B) (w x : W) :
    x⁻¹ ∈ doubleCoset cs J I w⁻¹ ↔ x ∈ doubleCoset cs I J w := by
  constructor
  · intro h
    simpa using inv_mem_doubleCoset cs h
  · exact inv_mem_doubleCoset cs

@[simp]
theorem isMinimal_inv_iff (I J : Finset B) (w : W) :
    IsMinimal cs J I w⁻¹ ↔ IsMinimal cs I J w := by
  constructor
  · intro h
    simpa using isMinimal_inv cs h
  · exact isMinimal_inv cs

@[simp]
theorem inv_mem_minimalReps_iff [Fintype W] (I J : Finset B) (w : W) :
    w⁻¹ ∈ minimalReps cs J I ↔ w ∈ minimalReps cs I J := by
  simp only [mem_minimalReps, isMinimal_inv_iff]

/-- Inversion exchanges the two literal finite sets of minimal representatives. -/
def minimalRepsInvEquiv [Fintype W] (I J : Finset B) :
    {w : W // w ∈ minimalReps cs I J} ≃
      {w : W // w ∈ minimalReps cs J I} where
  toFun w := ⟨w.val⁻¹, (inv_mem_minimalReps_iff cs I J w).mpr w.property⟩
  invFun w := ⟨w.val⁻¹, (inv_mem_minimalReps_iff cs J I w).mpr w.property⟩
  left_inv w := Subtype.ext (inv_inv w.val)
  right_inv w := Subtype.ext (inv_inv w.val)

@[simp]
theorem minimalRepsInvEquiv_apply_val [Fintype W] (I J : Finset B)
    (w : {w : W // w ∈ minimalReps cs I J}) :
    (minimalRepsInvEquiv cs I J w).val = w.val⁻¹ := rfl

@[simp]
theorem minimalRepsInvEquiv_symm_apply_val [Fintype W] (I J : Finset B)
    (w : {w : W // w ∈ minimalReps cs J I}) :
    ((minimalRepsInvEquiv cs I J).symm w).val = w.val⁻¹ := rfl

/-- Reindex a sum whose summands may depend on the minimality witness. -/
theorem sum_minimalRepsInvEquiv [Fintype W] {A : Type uA} [AddCommMonoid A]
    (I J : Finset B) (f : {w : W // w ∈ minimalReps cs J I} → A) :
    (∑ w : {w : W // w ∈ minimalReps cs I J},
      f (minimalRepsInvEquiv cs I J w)) =
        ∑ w : {w : W // w ∈ minimalReps cs J I}, f w := by
  classical
  exact Fintype.sum_equiv (minimalRepsInvEquiv cs I J) _ _ (fun _ => rfl)

/-- The same inversion reindexing for ambient-group-valued indices. -/
theorem sum_minimalReps_inv [Fintype W] {A : Type uA} [AddCommMonoid A]
    (I J : Finset B) (f : W → A) :
    (∑ w ∈ minimalReps cs I J, f w⁻¹) =
      ∑ w ∈ minimalReps cs J I, f w := by
  classical
  exact Finset.sum_equiv (Equiv.inv W)
    (fun w => (inv_mem_minimalReps_iff cs I J w).symm) (fun _ _ => rfl)

end Langlands.Group.RelativeWeylIndexing

namespace Langlands.Group.RelativeWeyl

universe uG

variable {G : Type uG} [Group G] (T : Subgroup G)

/-- The section corresponding to inverse Weyl elements, with inverse lifts. -/
def inverseSection (lift : Weyl T → normalizer T) : Weyl T → normalizer T :=
  fun w => (lift w⁻¹)⁻¹

@[simp]
theorem inverseSection_apply (lift : Weyl T → normalizer T) (w : Weyl T) :
    inverseSection T lift w = (lift w⁻¹)⁻¹ := rfl

theorem inverseSection_mk (lift : Weyl T → normalizer T)
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w) (w : Weyl T) :
    QuotientGroup.mk (inverseSection T lift w) = w := by
  simp only [inverseSection, QuotientGroup.mk_inv, hlift, inv_inv]

@[simp]
theorem inverseSection_involutive (lift : Weyl T → normalizer T) :
    inverseSection T (inverseSection T lift) = lift := by
  funext w
  simp only [inverseSection, inv_inv]

end Langlands.Group.RelativeWeyl
