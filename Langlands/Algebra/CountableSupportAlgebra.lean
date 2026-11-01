import Langlands.Algebra.IdempotentedRing
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Data.Set.Countable

/-!
Countably supported functions: a derived prerequisite motivated by Renard I.5.3.
The source gives no example in that passage; this module does not prove nonprojectivity.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.CountableSupportAlgebra

universe uR uX uI

variable (R : Type uR) [CommRing R] (X : Type uX)

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The pointwise nonunital algebra of functions with countable support. -/
def algebra : NonUnitalSubalgebra R (X → R) where
  carrier := {f | (Function.support f).Countable}
  zero_mem' := by
    change (Function.support (0 : X → R)).Countable
    simpa only [Function.support_zero] using (Set.countable_empty : (∅ : Set X).Countable)
  add_mem' := by
    intro f g hf hg
    apply (hf.union hg).mono
    intro x hx
    change f x + g x ≠ 0 at hx
    by_cases hfx : f x = 0
    · right
      change g x ≠ 0
      intro hgx
      exact hx (by simp [hfx, hgx])
    · exact Or.inl hfx
  mul_mem' := by
    intro f g hf _hg
    apply hf.mono
    intro x hx
    change f x * g x ≠ 0 at hx
    change f x ≠ 0
    intro hfx
    exact hx (by simp [hfx])
  smul_mem' := by
    intro c f hf
    apply hf.mono
    intro x hx
    change c * f x ≠ 0 at hx
    change f x ≠ 0
    intro hfx
    exact hx (by simp [hfx])

/-- The original function carrier, with inherited pointwise operations. -/
abbrev Carrier := ↥(algebra R X)

variable {R X}

@[simp] theorem mem_algebra (f : X → R) :
    f ∈ algebra R X ↔ (Function.support f).Countable := Iff.rfl

theorem support_countable (a : Carrier R X) : (Function.support a.val).Countable :=
  a.property

@[simp] theorem zero_apply (x : X) : (0 : Carrier R X).val x = 0 := rfl

@[simp] theorem add_apply (a b : Carrier R X) (x : X) :
    (a + b).val x = a.val x + b.val x := rfl

@[simp] theorem neg_apply (a : Carrier R X) (x : X) :
    (-a).val x = -a.val x := rfl

@[simp] theorem sub_apply (a b : Carrier R X) (x : X) :
    (a - b).val x = a.val x - b.val x := rfl

@[simp] theorem mul_apply (a b : Carrier R X) (x : X) :
    (a * b).val x = a.val x * b.val x := rfl

@[simp] theorem smul_apply (c : R) (a : Carrier R X) (x : X) :
    (c • a).val x = c * a.val x := rfl

/-- The indicator of a countable subset belongs to the actual algebra. -/
def indicator (S : Set X) (hS : S.Countable) : Carrier R X :=
  ⟨fun x => if x ∈ S then 1 else 0, by
    apply hS.mono
    intro x hx
    change (if x ∈ S then (1 : R) else 0) ≠ 0 at hx
    by_contra h
    exact hx (by simp [h])⟩

@[simp] theorem indicator_apply (S : Set X) (hS : S.Countable) (x : X) :
    (indicator (R := R) S hS).val x = if x ∈ S then 1 else 0 := rfl

/-- The displayed characteristic function is idempotent for pointwise multiplication. -/
def indicatorIdempotent (S : Set X) (hS : S.Countable) :
    Idempotent (Carrier R X) :=
  ⟨indicator S hS, by
    apply Subtype.ext
    funext x
    change (if x ∈ S then (1 : R) else 0) * (if x ∈ S then 1 else 0) =
      (if x ∈ S then 1 else 0)
    split_ifs <;> simp⟩

/-- The indicator of a containing set fixes the original function on the left. -/
theorem indicator_mul_eq (S : Set X) (hS : S.Countable) (a : Carrier R X)
    (ha : Function.support a.val ⊆ S) :
    indicator S hS * a = a := by
  apply Subtype.ext
  funext x
  change (if x ∈ S then (1 : R) else 0) * a.val x = a.val x
  by_cases hx : a.val x = 0
  · simp [hx]
  · simp [ha hx]

/-- The same indicator fixes a supported function on the right. -/
theorem mul_indicator_eq (S : Set X) (hS : S.Countable) (a : Carrier R X)
    (ha : Function.support a.val ⊆ S) :
    a * indicator S hS = a :=
  (mul_comm _ _).trans (indicator_mul_eq S hS a ha)

/-- Countably many original functions have a single two-sided idempotent local unit. -/
theorem countable_local_units {I : Type uI} [Countable I] (a : I → Carrier R X) :
    ∃ e : Idempotent (Carrier R X),
      ∀ i, (e : Carrier R X) * a i = a i ∧ a i * (e : Carrier R X) = a i := by
  let S : Set X := ⋃ i, Function.support (a i).val
  have hS : S.Countable := Set.countable_iUnion fun i => (a i).property
  refine ⟨indicatorIdempotent S hS, fun i => ?_⟩
  change indicator S hS * a i = a i ∧ a i * indicator S hS = a i
  have hi : indicator S hS * a i = a i :=
    indicator_mul_eq S hS (a i)
      (Set.subset_iUnion (fun j => Function.support (a j).val) i)
  exact ⟨hi, (mul_comm _ _).trans hi⟩

/-- In particular, this actual nonunital algebra is idempotented in Renard's sense. -/
theorem isIdempotented : IsIdempotented (Carrier R X) := by
  intro s
  obtain ⟨e, he⟩ := countable_local_units (fun a : s => a.val)
  refine ⟨e, fun a ha => ?_⟩
  exact (Idempotent.sandwich_eq_iff e a).mpr (he ⟨a, ha⟩)

/-- On an uncountable base, no element is a left identity for the whole algebra. -/
theorem no_left_identity [Nontrivial R] [Uncountable X] :
    ¬ ∃ e : Carrier R X, ∀ a : Carrier R X, e * a = a := by
  rintro ⟨e, he⟩
  have huniv : Function.support e.val = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx := congrArg (fun a : Carrier R X => a.val x)
      (he (indicator {x} (Set.countable_singleton x)))
    have heq : e.val x = 1 := by simpa using hx
    change e.val x ≠ 0
    rw [heq]
    exact one_ne_zero
  have hc : (Function.support e.val).Countable := e.property
  rw [huniv] at hc
  exact Set.not_countable_univ hc

/-! Complete interfaces keep coefficient, base-set and family universes independent. -/

example : NonUnitalCommRing (Carrier R X) := inferInstance
example : Module R (Carrier R X) := inferInstance
example : IsScalarTower R (Carrier R X) (Carrier R X) := inferInstance
example : SMulCommClass R (Carrier R X) (Carrier R X) := inferInstance
example : IsIdempotented (Carrier R X) := isIdempotented

end Langlands.Algebra.CountableSupportAlgebra
