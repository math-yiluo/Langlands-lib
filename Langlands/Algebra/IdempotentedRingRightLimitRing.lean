import Langlands.Algebra.IdempotentedRingRightLimit
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# The actual ring on right-compatible families

Renard I.1.3, printed p.9/PDF15. The source's product is constructed on
the actual additive inverse limit, using finite local units.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace IdempotentedRingRightLimit

universe uA

variable {A : Type uA} [NonUnitalRing A]

/-- A left local unit for one original ring element. -/
private theorem exists_leftUnit (hA : IsIdempotented A) (a : A) :
    ∃ e : Idempotent A, (e : A) * a = a := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a}
  exact ⟨e, (he a (by simp)).1⟩

/-- The value used to multiply a family by an original element is independent
of the left local unit chosen for that element. -/
theorem coordinate_mul_independent (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e f : Idempotent A)
    (he : (e : A) * a = a) (hf : (f : A) * a = a) :
    x.val e * a = x.val f * a := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have heg : e ≤ g := hg e (by simp)
  have hfg : f ≤ g := hg f (by simp)
  calc
    x.val e * a = (x.val g * (e : A)) * a := by
      rw [x.property.2 e g heg]
    _ = x.val g * a := by rw [mul_assoc, he]
    _ = (x.val g * (f : A)) * a := by rw [mul_assoc, hf]
    _ = x.val f * a := by rw [x.property.2 f g hfg]

/-- Internal evaluation of a compatible family on an original ring element. -/
def applyOriginal (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) : A :=
  x.val (Classical.choose (exists_leftUnit hA a)) * a

/-- Every left local unit computes the same internal evaluation. -/
theorem applyOriginal_eq (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (he : (e : A) * a = a) :
    applyOriginal hA x a = x.val e * a :=
  coordinate_mul_independent hA x a _ e
    (Classical.choose_spec (exists_leftUnit hA a)) he

@[simp] theorem applyOriginal_zero (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) : applyOriginal hA x 0 = 0 := by
  obtain ⟨e, he⟩ := exists_leftUnit hA (0 : A)
  rw [applyOriginal_eq hA x 0 e he, mul_zero]

theorem applyOriginal_add (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a b : A) :
    applyOriginal hA x (a + b) =
      applyOriginal hA x a + applyOriginal hA x b := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a, b}
  have hea : (e : A) * a = a := (he a (by simp)).1
  have heb : (e : A) * b = b := (he b (by simp)).1
  have heab : (e : A) * (a + b) = a + b := by rw [mul_add, hea, heb]
  rw [applyOriginal_eq hA x (a + b) e heab,
    applyOriginal_eq hA x a e hea, applyOriginal_eq hA x b e heb, mul_add]

/-- Internal evaluation is a homomorphism of right regular modules. -/
theorem applyOriginal_mul (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a b : A) :
    applyOriginal hA x (a * b) = applyOriginal hA x a * b := by
  obtain ⟨e, he⟩ := exists_leftUnit hA a
  have heab : (e : A) * (a * b) = a * b := by rw [← mul_assoc, he]
  rw [applyOriginal_eq hA x (a * b) e heab,
    applyOriginal_eq hA x a e he, mul_assoc]

@[simp] theorem zero_applyOriginal (hA : IsIdempotented A) (a : A) :
    applyOriginal hA (0 : IdempotentedRingRightLimit A) a = 0 := by
  obtain ⟨e, he⟩ := exists_leftUnit hA a
  rw [applyOriginal_eq hA 0 a e he]
  exact zero_mul a

theorem add_applyOriginal (hA : IsIdempotented A)
    (x y : IdempotentedRingRightLimit A) (a : A) :
    applyOriginal hA (x + y) a = applyOriginal hA x a + applyOriginal hA y a := by
  obtain ⟨e, he⟩ := exists_leftUnit hA a
  rw [applyOriginal_eq hA (x + y) a e he,
    applyOriginal_eq hA x a e he, applyOriginal_eq hA y a e he]
  exact add_mul (x.val e) (y.val e) a

@[simp] theorem applyOriginal_idempotent (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A) :
    applyOriginal hA x (e : A) = x.val e := by
  rw [applyOriginal_eq hA x (e : A) e e.property]
  exact x.property.1 e

@[simp] theorem canonical_applyOriginal (hA : IsIdempotented A) (a b : A) :
    applyOriginal hA (canonical a) b = a * b := by
  obtain ⟨e, he⟩ := exists_leftUnit hA b
  rw [applyOriginal_eq hA (canonical a) b e he]
  change (a * (e : A)) * b = a * b
  rw [mul_assoc, he]

/-- The source's actual product on compatible families. -/
def product (hA : IsIdempotented A)
    (x y : IdempotentedRingRightLimit A) : IdempotentedRingRightLimit A :=
  ⟨fun e => applyOriginal hA x (y.val e), by
    constructor
    · intro e
      change applyOriginal hA x (y.val e) * (e : A) = applyOriginal hA x (y.val e)
      rw [← applyOriginal_mul, y.property.1 e]
    · intro e f hef
      change applyOriginal hA x (y.val f) * (e : A) = applyOriginal hA x (y.val e)
      rw [← applyOriginal_mul, y.property.2 e f hef]⟩

/-- The exact source formula holds for every permitted choice of `f`. -/
theorem product_val (hA : IsIdempotented A)
    (x y : IdempotentedRingRightLimit A) (e f : Idempotent A)
    (hf : (f : A) * y.val e = y.val e) :
    (product hA x y).val e = x.val f * y.val e :=
  applyOriginal_eq hA x (y.val e) f hf

/-- Product corresponds to composition of internal evaluation. -/
theorem product_applyOriginal (hA : IsIdempotented A)
    (x y : IdempotentedRingRightLimit A) (a : A) :
    applyOriginal hA (product hA x y) a =
      applyOriginal hA x (applyOriginal hA y a) := by
  obtain ⟨e, he⟩ := exists_leftUnit hA a
  rw [applyOriginal_eq hA (product hA x y) a e he,
    applyOriginal_eq hA y a e he, applyOriginal_mul]
  rfl

/-- The source's actual unit family, with value `e` at `e`. -/
def unit : IdempotentedRingRightLimit A :=
  ⟨fun e => (e : A), by
    constructor
    · intro e
      exact e.property
    · intro e f hef
      exact ((Idempotent.le_iff_mul e f).mp hef).1⟩

@[simp] theorem unit_val (e : Idempotent A) : (unit (A := A)).val e = (e : A) := rfl

@[simp] theorem unit_applyOriginal (hA : IsIdempotented A) (a : A) :
    applyOriginal hA unit a = a := by
  obtain ⟨e, he⟩ := exists_leftUnit hA a
  rw [applyOriginal_eq hA unit a e he]
  exact he

/-- Associativity for the actual product. -/
theorem product_assoc (hA : IsIdempotented A) (x y z : IdempotentedRingRightLimit A) :
    product hA (product hA x y) z = product hA x (product hA y z) := by
  apply Subtype.ext
  funext e
  exact product_applyOriginal hA x y (z.val e)

theorem product_add (hA : IsIdempotented A) (x y z : IdempotentedRingRightLimit A) :
    product hA x (y + z) = product hA x y + product hA x z := by
  apply Subtype.ext
  funext e
  exact applyOriginal_add hA x (y.val e) (z.val e)

theorem add_product (hA : IsIdempotented A) (x y z : IdempotentedRingRightLimit A) :
    product hA (x + y) z = product hA x z + product hA y z := by
  apply Subtype.ext
  funext e
  exact add_applyOriginal hA x y (z.val e)

@[simp] theorem product_zero (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) :
    product hA x 0 = 0 := by
  apply Subtype.ext
  funext e
  exact applyOriginal_zero hA x

@[simp] theorem zero_product (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) :
    product hA 0 x = 0 := by
  apply Subtype.ext
  funext e
  exact zero_applyOriginal hA (x.val e)

@[simp] theorem product_unit (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) :
    product hA x unit = x := by
  apply Subtype.ext
  funext e
  exact applyOriginal_idempotent hA x e

@[simp] theorem unit_product (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) :
    product hA unit x = x := by
  apply Subtype.ext
  funext e
  exact unit_applyOriginal hA (x.val e)

/-- The actual unital ring, retaining the original pointwise additive group. -/
@[instance_reducible]
def ring (hA : IsIdempotented A) : Ring (IdempotentedRingRightLimit A) where
  __ := (inferInstance : AddCommGroup (IdempotentedRingRightLimit A))
  mul := product hA
  one := unit
  mul_assoc := product_assoc hA
  one_mul := unit_product hA
  mul_one := product_unit hA
  left_distrib := product_add hA
  right_distrib := add_product hA
  zero_mul := zero_product hA
  mul_zero := product_zero hA

/-- The actual canonical embedding preserves original multiplication. -/
theorem canonical_product (hA : IsIdempotented A) (a b : A) :
    canonical (a * b) = product hA (canonical a) (canonical b) := by
  apply Subtype.ext
  funext e
  change (a * b) * (e : A) = applyOriginal hA (canonical a) (b * (e : A))
  rw [canonical_applyOriginal, mul_assoc]

/-- The actual canonical additive map as a nonunital ring homomorphism. -/
def canonicalRingHom (hA : IsIdempotented A) :
    letI := ring hA
    A →ₙ+* IdempotentedRingRightLimit A := by
  letI := ring hA
  exact
    { canonical (A := A) with
      map_mul' := fun a b => canonical_product hA a b }

@[simp] theorem canonicalRingHom_apply (hA : IsIdempotented A) (a : A) :
    canonicalRingHom hA a = canonical a := rfl

@[simp] theorem canonicalRingHom_toAddMonoidHom (hA : IsIdempotented A) :
    letI := ring hA
    (canonicalRingHom hA).toAddMonoidHom = canonical (A := A) := rfl

theorem canonicalRingHom_injective (hA : IsIdempotented A) :
    Function.Injective (canonicalRingHom hA) :=
  canonical_injective hA

/-! Complete unapplied interfaces at the arbitrary original ring universe. -/

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    Ring (IdempotentedRingRightLimit A) :=
  @ring.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (x : IdempotentedRingRightLimit A) → (a : A) → (e f : Idempotent A) →
    (e : A) * a = a → (f : A) * a = a → x.val e * a = x.val f * a :=
  @coordinate_mul_independent.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (a : A) → (e : Idempotent A) →
    (e : A) * a = a → applyOriginal hA x a = x.val e * a :=
  @applyOriginal_eq.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightLimit A → IdempotentedRingRightLimit A →
      IdempotentedRingRightLimit A :=
  @product.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x y : IdempotentedRingRightLimit A) → (e f : Idempotent A) →
    (f : A) * y.val e = y.val e →
    (product hA x y).val e = x.val f * y.val e :=
  @product_val.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IdempotentedRingRightLimit A :=
  @unit.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a b : A) → canonical (a * b) = product hA (canonical a) (canonical b) :=
  @canonical_product.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := ring hA
    A →ₙ+* IdempotentedRingRightLimit A :=
  @canonicalRingHom.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := ring hA
    (canonicalRingHom hA).toAddMonoidHom = canonical (A := A) :=
  @canonicalRingHom_toAddMonoidHom.{uA}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    Function.Injective (canonicalRingHom hA) :=
  @canonicalRingHom_injective.{uA}

/-! The installed ring retains the entire published additive group definitionally. -/

example (hA : IsIdempotented A) :
    (ring hA).toAddCommGroup =
      (inferInstance : AddCommGroup (IdempotentedRingRightLimit A)) := rfl

example (hA : IsIdempotented A) :
    letI := ring hA
    ∀ (x y : IdempotentedRingRightLimit A) (e f : Idempotent A),
      (f : A) * y.val e = y.val e → (x * y).val e = x.val f * y.val e :=
  product_val hA

example (hA : IsIdempotented A) :
    letI := ring hA
    ∀ e : Idempotent A, (1 : IdempotentedRingRightLimit A).val e = (e : A) :=
  unit_val

example (hA : IsIdempotented A) :
    letI := ring hA
    ∀ a b : A, canonical (a * b) = canonical a * canonical b :=
  canonical_product hA

end IdempotentedRingRightLimit
end Langlands.Algebra
