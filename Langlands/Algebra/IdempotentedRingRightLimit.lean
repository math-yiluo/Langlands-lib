import Langlands.Algebra.IdempotentedRing
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The actual additive right-image inverse limit

Renard I.1.3, printed pp.8–9/PDF14–15. The inverse limit is constructed
from actual right images, not assumed as an external object.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uB

variable {A : Type uA} [NonUnitalRing A]

namespace Idempotent

/-- The source's `Ae`, as an additive subgroup of the original ring. -/
def rightImage (e : Idempotent A) : AddSubgroup A where
  carrier := {a | a * (e : A) = a}
  zero_mem' := zero_mul _
  add_mem' := by
    intro a b ha hb
    change (a + b) * (e : A) = a + b
    rw [add_mul, ha, hb]
  neg_mem' := by
    intro a ha
    change (-a) * (e : A) = -a
    rw [neg_mul, ha]

@[simp] theorem mem_rightImage (e : Idempotent A) (a : A) :
    a ∈ e.rightImage ↔ a * (e : A) = a := Iff.rfl

theorem mem_rightImage_iff_exists (e : Idempotent A) (a : A) :
    a ∈ e.rightImage ↔ ∃ b : A, b * (e : A) = a := by
  constructor
  · intro ha
    exact ⟨a, ha⟩
  · rintro ⟨b, rfl⟩
    exact e.property.mul_mul_self b

/-- The actual right projection onto `Ae`. -/
def rightProjection (e : Idempotent A) : A →+ e.rightImage where
  toFun a := ⟨a * (e : A), e.property.mul_mul_self a⟩
  map_zero' := Subtype.ext (zero_mul _)
  map_add' a b := Subtype.ext (add_mul a b (e : A))

@[simp] theorem coe_rightProjection (e : Idempotent A) (a : A) :
    (e.rightProjection a : A) = a * (e : A) := rfl

@[simp] theorem rightProjection_coe (e : Idempotent A) (a : e.rightImage) :
    e.rightProjection (a : A) = a := Subtype.ext a.property

theorem rightProjection_surjective (e : Idempotent A) :
    Function.Surjective e.rightProjection := by
  intro a
  exact ⟨a, rightProjection_coe e a⟩

/-- The inverse-system transition `Af → Ae` for `e ≤ f`. -/
def rightTransition {e f : Idempotent A} (_h : e ≤ f) :
    f.rightImage →+ e.rightImage :=
  e.rightProjection.comp f.rightImage.subtype

@[simp] theorem coe_rightTransition {e f : Idempotent A} (h : e ≤ f)
    (a : f.rightImage) : (rightTransition h a : A) = (a : A) * (e : A) := rfl

@[simp] theorem rightTransition_refl (e : Idempotent A) :
    rightTransition (le_refl e) = AddMonoidHom.id e.rightImage := by
  ext a
  exact a.property

theorem rightTransition_comp {e f g : Idempotent A} (hef : e ≤ f) (hfg : f ≤ g) :
    (rightTransition hef).comp (rightTransition hfg) =
      rightTransition (hef.trans hfg) := by
  ext a
  change ((a : A) * (f : A)) * (e : A) = (a : A) * (e : A)
  rw [mul_assoc, ((le_iff_mul e f).1 hef).1]

theorem rightTransition_projection {e f : Idempotent A} (h : e ≤ f) :
    (rightTransition h).comp f.rightProjection = e.rightProjection := by
  ext a
  change (a * (f : A)) * (e : A) = a * (e : A)
  rw [mul_assoc, ((le_iff_mul e f).1 h).1]

end Idempotent

/-- The source's compatible families, as an actual additive subgroup. -/
def rightCompatibleFamilies (A : Type uA) [NonUnitalRing A] :
    AddSubgroup (Idempotent A → A) where
  carrier := {a | (∀ e, a e * (e : A) = a e) ∧
    ∀ e f, e ≤ f → a f * (e : A) = a e}
  zero_mem' := by
    constructor
    · intro e
      exact zero_mul _
    · intro e f h
      exact zero_mul _
  add_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    constructor
    · intro e
      change (a e + b e) * (e : A) = a e + b e
      rw [add_mul, ha, hb]
    · intro e f h
      change (a f + b f) * (e : A) = a e + b e
      rw [add_mul, hca e f h, hcb e f h]
  neg_mem' := by
    rintro a ⟨ha, hca⟩
    constructor
    · intro e
      change (-a e) * (e : A) = -a e
      rw [neg_mul, ha]
    · intro e f h
      change (-a f) * (e : A) = -a e
      rw [neg_mul, hca e f h]

/-- The actual additive inverse limit `lim Ae`; no topology or product is installed. -/
abbrev IdempotentedRingRightLimit (A : Type uA) [NonUnitalRing A] :=
  ↥(rightCompatibleFamilies A)

namespace IdempotentedRingRightLimit

/-- The actual coordinate in `Ae`. -/
def evaluation (e : Idempotent A) : IdempotentedRingRightLimit A →+ e.rightImage where
  toFun a := ⟨a.val e, a.property.1 e⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coe_evaluation (e : Idempotent A) (a : IdempotentedRingRightLimit A) :
    (evaluation e a : A) = a.val e := rfl

@[ext] theorem ext {a b : IdempotentedRingRightLimit A}
    (h : ∀ e, evaluation e a = evaluation e b) : a = b := by
  apply Subtype.ext
  funext e
  exact congrArg Subtype.val (h e)

theorem transition_evaluation {e f : Idempotent A} (h : e ≤ f) :
    (Idempotent.rightTransition h).comp (evaluation f) = evaluation e := by
  ext a
  exact a.property.2 e f h

/-- The canonical additive map `a ↦ (e ↦ a * e)`. -/
def canonical : A →+ IdempotentedRingRightLimit A where
  toFun a := ⟨fun e => a * (e : A), by
    constructor
    · intro e
      exact e.property.mul_mul_self a
    · intro e f h
      change (a * (f : A)) * (e : A) = a * (e : A)
      rw [mul_assoc, ((Idempotent.le_iff_mul e f).1 h).1]⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    exact zero_mul _
  map_add' a b := by
    apply Subtype.ext
    funext e
    exact add_mul a b (e : A)

@[simp] theorem canonical_val (a : A) (e : Idempotent A) :
    (canonical a).val e = a * (e : A) := rfl

@[simp] theorem evaluation_canonical (e : Idempotent A) :
    (evaluation e).comp canonical = e.rightProjection := rfl

theorem canonical_injective (hA : IsIdempotented A) :
    Function.Injective (canonical (A := A)) := by
  classical
  intro a b hab
  obtain ⟨e, he⟩ := hA {a, b}
  have ha := (Idempotent.sandwich_eq_iff e a).1 (he a (by simp))
  have hb := (Idempotent.sandwich_eq_iff e b).1 (he b (by simp))
  have h := congrArg (fun c : IdempotentedRingRightLimit A => c.val e) hab
  change a * (e : A) = b * (e : A) at h
  rwa [ha.2, hb.2] at h

variable {B : Type uB} [AddCommGroup B]

/-- The unique additive map induced by an actual compatible cone. -/
def lift (q : ∀ e : Idempotent A, B →+ e.rightImage)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e) :
    B →+ IdempotentedRingRightLimit A where
  toFun b := ⟨fun e => (q e b : A), by
    constructor
    · intro e
      exact (q e b).property
    · intro e f h
      exact congrArg Subtype.val (DFunLike.congr_fun (hq e f h) b)⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    change (q e 0 : A) = 0
    rw [map_zero]
    rfl
  map_add' b c := by
    apply Subtype.ext
    funext e
    change (q e (b + c) : A) = (q e b : A) + (q e c : A)
    rw [map_add]
    rfl

@[simp] theorem evaluation_lift (q : ∀ e : Idempotent A, B →+ e.rightImage)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e) (e : Idempotent A) :
    (evaluation e).comp (lift q hq) = q e := rfl

theorem lift_unique (q : ∀ e : Idempotent A, B →+ e.rightImage)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e)
    (l : B →+ IdempotentedRingRightLimit A)
    (hl : ∀ e, (evaluation e).comp l = q e) : l = lift q hq := by
  apply AddMonoidHom.ext
  intro b
  apply ext
  intro e
  exact DFunLike.congr_fun (hl e) b

/-- The exact additive inverse-limit universal property of the actual family group. -/
theorem existsUnique_lift (q : ∀ e : Idempotent A, B →+ e.rightImage)
    (hq : ∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e) :
    ∃! l : B →+ IdempotentedRingRightLimit A,
      ∀ e, (evaluation e).comp l = q e :=
  ⟨lift q hq, evaluation_lift q hq, fun l hl => lift_unique q hq l hl⟩

/-! Complete unapplied interfaces preserve independent ring and test-group universes. -/

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    Function.Injective (canonical (A := A)) :=
  @canonical_injective.{uA}

example : {A : Type uA} → [NonUnitalRing A] → {B : Type uB} → [AddCommGroup B] →
    (q : ∀ e : Idempotent A, B →+ e.rightImage) →
    (∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e) →
    ∃! l : B →+ IdempotentedRingRightLimit A,
      ∀ e, (evaluation e).comp l = q e :=
  @existsUnique_lift.{uA, uB}

example : {A : Type} → [NonUnitalRing A] → {B : Type 1} → [AddCommGroup B] →
    (q : ∀ e : Idempotent A, B →+ e.rightImage) →
    (∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e) →
    ∃! l : B →+ IdempotentedRingRightLimit A,
      ∀ e, (evaluation e).comp l = q e :=
  @existsUnique_lift.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → {B : Type} → [AddCommGroup B] →
    (q : ∀ e : Idempotent A, B →+ e.rightImage) →
    (∀ (e f : Idempotent A) (h : e ≤ f),
      (Idempotent.rightTransition h).comp (q f) = q e) →
    ∃! l : B →+ IdempotentedRingRightLimit A,
      ∀ e, (evaluation e).comp l = q e :=
  @existsUnique_lift.{1, 0}

end IdempotentedRingRightLimit
end Langlands.Algebra
