import Mathlib.Algebra.Ring.Idempotent
import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Indexed

/-!
# Idempotents, corners, and rings with finite local units

The ring core of Renard (9 July 2026), I.1.1–I.1.2. All ambient rings are
associative and may be noncommutative and nonunital.
-/

namespace Langlands.Algebra

universe u v

/-- Actual idempotent elements, with a dedicated type to keep the corner order
independent of any order on the ambient ring. -/
structure Idempotent (A : Type u) [Mul A] where
  val : A
  property : IsIdempotentElem val

namespace Idempotent

instance {A : Type u} [Mul A] : Coe (Idempotent A) A := ⟨Idempotent.val⟩

@[ext] theorem ext {A : Type u} [Mul A] {e f : Idempotent A}
    (h : (e : A) = (f : A)) : e = f := by
  cases e
  cases f
  cases h
  rfl

variable {A : Type u} [NonUnitalRing A]

/-- A sandwich is fixed exactly when both multiplications fix the element. -/
theorem sandwich_eq_iff (e : Idempotent A) (a : A) :
    (e : A) * a * e = a ↔ (e : A) * a = a ∧ a * e = a := by
  constructor
  · intro h
    constructor
    · calc
        (e : A) * a = e * (e * a * e) := congrArg ((e : A) * ·) h.symm
        _ = e * a * e := by simp only [← mul_assoc, e.property.eq]
        _ = a := h
    · calc
        a * (e : A) = (e * a * e) * e := congrArg (· * (e : A)) h.symm
        _ = e * a * e := e.property.mul_mul_self _
        _ = a := h
  · rintro ⟨hl, hr⟩
    rw [hl, hr]

/-- The actual corner `eAe`, realized as a nonunital subring of `A`. -/
def corner (e : Idempotent A) : NonUnitalSubring A where
  carrier := {a | (e : A) * a * e = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change (e : A) * (a + b) * e = a + b
    simpa only [mul_add, add_mul] using congrArg₂ (· + ·) ha hb
  neg_mem' := by
    intro a ha
    change (e : A) * (-a) * e = -a
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg ha
  mul_mem' := by
    intro a b ha hb
    apply (sandwich_eq_iff e (a * b)).mpr
    exact ⟨by rw [← mul_assoc, ((sandwich_eq_iff e a).mp ha).1],
      by rw [mul_assoc, ((sandwich_eq_iff e b).mp hb).2]⟩

@[simp] theorem mem_corner (e : Idempotent A) (a : A) :
    a ∈ e.corner ↔ (e : A) * a * e = a := Iff.rfl

theorem mem_corner_iff (e : Idempotent A) (a : A) :
    a ∈ e.corner ↔ (e : A) * a = a ∧ a * e = a := sandwich_eq_iff e a

@[simp] theorem self_mem_corner (e : Idempotent A) : (e : A) ∈ e.corner := by
  change (e : A) * e * e = e
  rw [e.property.eq, e.property.eq]

/-- The fixed-point corner is precisely the image of the sandwich map. -/
theorem mem_corner_iff_exists (e : Idempotent A) (a : A) :
    a ∈ e.corner ↔ ∃ b : A, (e : A) * b * e = a := by
  constructor
  · intro ha
    exact ⟨a, ha⟩
  · rintro ⟨b, rfl⟩
    change (e : A) * (e * b * e) * e = e * b * e
    simp only [← mul_assoc, e.property.eq, e.property.mul_mul_self]

/-- The equality `eAe = eA ∩ Ae`, expressed by membership in the two images. -/
theorem mem_corner_iff_left_right_image (e : Idempotent A) (a : A) :
    a ∈ e.corner ↔ (∃ b : A, (e : A) * b = a) ∧ ∃ c : A, c * e = a := by
  rw [mem_corner_iff]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨⟨a, hl⟩, ⟨a, hr⟩⟩
  · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩⟩
    constructor
    · rw [← hb, e.property.mul_self_mul]
    · rw [← hc, e.property.mul_mul_self]

/-- The corner as a type, carrying the inherited operations and the unit `e`. -/
def Corner (e : Idempotent A) := ↥e.corner

namespace Corner

variable (e : Idempotent A)

instance : NonUnitalRing (Corner e) := inferInstanceAs (NonUnitalRing ↥e.corner)

instance : One (Corner e) := ⟨⟨e, e.self_mem_corner⟩⟩

/-- The actual inclusion into the possibly nonunital ambient ring. -/
def toAmbient : Corner e →ₙ+* A := NonUnitalSubringClass.subtype e.corner

theorem toAmbient_injective : Function.Injective (toAmbient e) := Subtype.coe_injective

@[simp] theorem toAmbient_one : toAmbient e 1 = (e : A) := rfl

instance ring : Ring (Corner e) where
  __ : NonUnitalRing (Corner e) := inferInstance
  one := 1
  one_mul a := Subtype.ext ((mem_corner_iff e a.val).mp a.property).1
  mul_one a := Subtype.ext ((mem_corner_iff e a.val).mp a.property).2
  natCast n := n • (1 : Corner e)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • (1 : Corner e)
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

end Corner

/-- Corner inclusion is equivalent to the smaller idempotent lying in the larger corner. -/
theorem corner_le_iff_mem (e f : Idempotent A) :
    e.corner ≤ f.corner ↔ (e : A) ∈ f.corner := by
  constructor
  · intro h
    exact h e.self_mem_corner
  · intro h a ha
    obtain ⟨hfe, hef⟩ := (mem_corner_iff f e).mp h
    obtain ⟨hea, hae⟩ := (mem_corner_iff e a).mp ha
    apply (mem_corner_iff f a).mpr
    constructor
    · calc
        (f : A) * a = f * (e * a) := congrArg ((f : A) * ·) hea.symm
        _ = a := by rw [← mul_assoc, hfe, hea]
    · calc
        a * (f : A) = (a * e) * f := congrArg (· * (f : A)) hae.symm
        _ = a := by rw [mul_assoc, hef, hae]

/-- Renard's order on idempotents is inclusion of their actual corners. -/
instance : PartialOrder (Idempotent A) where
  le e f := e.corner ≤ f.corner
  le_refl e := le_refl e.corner
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  le_antisymm e f hef hfe := by
    have h₁ := (mem_corner_iff f e).mp ((corner_le_iff_mem e f).mp hef)
    have h₂ := (mem_corner_iff e f).mp ((corner_le_iff_mem f e).mp hfe)
    exact Idempotent.ext (h₁.2.symm.trans h₂.1)

theorem le_iff_corner_le (e f : Idempotent A) : e ≤ f ↔ e.corner ≤ f.corner := Iff.rfl

theorem le_iff_mem_corner (e f : Idempotent A) : e ≤ f ↔ (e : A) ∈ f.corner :=
  corner_le_iff_mem e f

theorem le_iff_sandwich (e f : Idempotent A) :
    e ≤ f ↔ (f : A) * e * f = e := le_iff_mem_corner e f

theorem le_iff_mul (e f : Idempotent A) :
    e ≤ f ↔ (f : A) * e = e ∧ (e : A) * f = e := by
  rw [le_iff_mem_corner, mem_corner_iff]

/-- I.1.1(ii): a larger idempotent absorbs every element fixed on the left. -/
theorem mul_eq_of_le {e f : Idempotent A} (h : e ≤ f) {a : A}
    (ha : (e : A) * a = a) : (f : A) * a = a := by
  calc
    (f : A) * a = f * (e * a) := congrArg ((f : A) * ·) ha.symm
    _ = a := by rw [← mul_assoc, ((le_iff_mul e f).mp h).1, ha]

/-- The corresponding right absorption law. -/
theorem mul_eq_of_le_right {e f : Idempotent A} (h : e ≤ f) {a : A}
    (ha : a * (e : A) = a) : a * (f : A) = a := by
  calc
    a * (f : A) = (a * e) * f := congrArg (· * (f : A)) ha.symm
    _ = a := by rw [mul_assoc, ((le_iff_mul e f).mp h).2, ha]

namespace Corner

/-- Corner inclusions preserve addition and multiplication, but need not preserve units. -/
def inclusion {e f : Idempotent A} (h : e ≤ f) : Corner e →ₙ+* Corner f :=
  NonUnitalSubring.inclusion h

@[simp] theorem toAmbient_inclusion {e f : Idempotent A} (h : e ≤ f) (a : Corner e) :
    toAmbient f (inclusion h a) = toAmbient e a := rfl

theorem inclusion_injective {e f : Idempotent A} (h : e ≤ f) :
    Function.Injective (inclusion h) := by
  intro a b hab
  exact (toAmbient_injective e) (congrArg (toAmbient f) hab)

@[simp] theorem toAmbient_inclusion_one {e f : Idempotent A} (h : e ≤ f) :
    toAmbient f (inclusion h 1) = (e : A) := rfl

end Corner
end Idempotent

/-- Renard's idempotented-ring condition: every finite set is in a single corner. -/
def IsIdempotented (A : Type u) [NonUnitalRing A] : Prop :=
  ∀ s : Finset A, ∃ e : Idempotent A, ∀ a ∈ s, (e : A) * a * e = a

namespace IsIdempotented

variable {A : Type u} [NonUnitalRing A]

/-- Equivalently, each finite set has an idempotent two-sided local unit. -/
theorem iff_two_sided_local_units : IsIdempotented A ↔
    ∀ s : Finset A, ∃ e : Idempotent A,
      ∀ a ∈ s, (e : A) * a = a ∧ a * e = a := by
  simp only [IsIdempotented, Idempotent.sandwich_eq_iff]

/-- The definition also applies to finite sets given without a `Finset` enumeration. -/
theorem iff_finite_set : IsIdempotented A ↔
    ∀ s : Set A, s.Finite → ∃ e : Idempotent A, ∀ a ∈ s, (e : A) * a * e = a := by
  classical
  constructor
  · intro h s hs
    simpa only [Set.Finite.mem_toFinset] using h hs.toFinset
  · intro h s
    exact h s s.finite_toSet

/-- Every unital ring is idempotented, with its global identity as local unit. -/
theorem of_ring (R : Type u) [Ring R] : IsIdempotented R := by
  intro s
  exact ⟨⟨1, IsIdempotentElem.one⟩, by simp⟩

/-- Finite families in any independent index universe have a common local unit. -/
theorem finite_family (h : IsIdempotented A) {ι : Type v} [Finite ι] (a : ι → A) :
    ∃ e : Idempotent A, ∀ i, (e : A) * a i * e = a i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨e, he⟩ := h (Finset.univ.image a)
  exact ⟨e, fun i => he (a i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩

/-- I.1.2: every finite set of idempotents has an upper bound in the corner order. -/
theorem finite_upper_bound (h : IsIdempotented A) (s : Finset (Idempotent A)) :
    ∃ f : Idempotent A, ∀ e ∈ s, e ≤ f := by
  classical
  obtain ⟨f, hf⟩ := h (s.image Idempotent.val)
  refine ⟨f, fun e he => (Idempotent.le_iff_sandwich e f).mpr ?_⟩
  exact hf e (Finset.mem_image.mpr ⟨e, he, rfl⟩)

/-- The upper-bound property for finite families, including the empty family. -/
theorem finite_family_upper_bound (h : IsIdempotented A) {ι : Type v} [Finite ι]
    (e : ι → Idempotent A) : ∃ f : Idempotent A, ∀ i, e i ≤ f := by
  obtain ⟨f, hf⟩ := h.finite_family (fun i => (e i : A))
  exact ⟨f, fun i => (Idempotent.le_iff_sandwich (e i) f).mpr (hf i)⟩

/-- Every element lies in an actual unital corner. -/
theorem exists_mem_corner (h : IsIdempotented A) (a : A) :
    ∃ e : Idempotent A, a ∈ e.corner := by
  obtain ⟨e, he⟩ := h {a}
  exact ⟨e, he a (Finset.mem_singleton_self a)⟩

/-- The set-theoretic union of the corners is the whole ring. -/
theorem iUnion_corners (h : IsIdempotented A) :
    (⋃ e : Idempotent A, (e.corner : Set A)) = Set.univ := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact h.exists_mem_corner a

end IsIdempotented
end Langlands.Algebra
