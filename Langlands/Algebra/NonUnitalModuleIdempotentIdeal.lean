import Langlands.Algebra.IdempotentedRingRightLimit
import Langlands.Algebra.NonUnitalModuleCorner

/-!
# The actual left module Ae and its fixed-vector Hom correspondence

The construction used in Renard I.5.2, printed pp.26–27 / PDF32–33.
The carrier is the published right image, lifted only to control its universe.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleIdempotentIdeal

open CategoryTheory NonUnitalModuleCorner

universe uA uL uM uN

variable {A : Type uA} [NonUnitalRing A]

/-- The actual subgroup `Ae`, lifted to the chosen carrier universe. -/
def Carrier (e : Idempotent A) := ULift.{uL} ↥e.rightImage

instance carrierAddCommGroup (e : Idempotent A) : AddCommGroup (Carrier.{uA, uL} e) :=
  inferInstanceAs (AddCommGroup (ULift.{uL} ↥e.rightImage))

/-- Left multiplication preserves precisely the published subgroup `Ae`. -/
instance action (e : Idempotent A) : NonUnitalModule A (Carrier.{uA, uL} e) where
  smul a x := ULift.up ⟨a * x.down.val, by
    change (a * x.down.val) * (e : A) = a * x.down.val
    rw [mul_assoc, x.down.property]⟩
  smul_zero a := congrArg ULift.up (Subtype.ext (mul_zero a))
  smul_add a x y := congrArg ULift.up (Subtype.ext (mul_add a x.down.val y.down.val))
  mul_smul a b x := congrArg ULift.up (Subtype.ext (mul_assoc a b x.down.val))
  add_smul a b x := congrArg ULift.up (Subtype.ext (add_mul a b x.down.val))
  zero_smul x := congrArg ULift.up (Subtype.ext (zero_mul x.down.val))

@[simp] theorem smul_down_val (e : Idempotent A) (a : A)
    (x : Carrier.{uA, uL} e) : (a • x).down.val = a * x.down.val := rfl

/-- The distinguished vector is the original idempotent itself. -/
def generator (e : Idempotent A) : Carrier.{uA, uL} e :=
  ULift.up ⟨(e : A), e.property.eq⟩

@[simp] theorem generator_down_val (e : Idempotent A) :
    (generator.{uA, uL} e).down.val = (e : A) := rfl

@[simp] theorem generator_fixed (e : Idempotent A) :
    (e : A) • generator.{uA, uL} e = generator e :=
  congrArg ULift.up (Subtype.ext e.property.eq)

/-- Every vector of `Ae` is its own ambient coefficient times `e`. -/
theorem smul_generator (e : Idempotent A) (x : Carrier.{uA, uL} e) :
    x.down.val • generator e = x :=
  congrArg ULift.up (Subtype.ext x.down.property)

/-- A local unit for the original ring element fixes the same ideal vector. -/
theorem isNondegenerate (hA : IsIdempotented A) (e : Idempotent A) :
    IsNondegenerate A (Carrier.{uA, uL} e) := by
  classical
  intro x
  obtain ⟨f, hf⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {x.down.val}
  exact ⟨f, congrArg ULift.up (Subtype.ext (hf x.down.val (by simp)).1)⟩

/-- The actual ideal object in the original nondegenerate-module category. -/
def object (hA : IsIdempotented A) (e : Idempotent A) :
    NondegenerateModuleCat.{uA, max uA uL} A :=
  ⟨NonUnitalModuleCat.of A (Carrier.{uA, uL} e), isNondegenerate hA e⟩

theorem object_carrier (hA : IsIdempotented A) (e : Idempotent A) :
    ((object.{uA, uL} hA e).obj : Type (max uA uL)) = Carrier.{uA, uL} e := rfl

theorem object_action (hA : IsIdempotented A) (e : Idempotent A) :
    @NonUnitalModuleCat.isModule A _ (object.{uA, uL} hA e).obj = action e := rfl

variable {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [NonUnitalModule A M] [NonUnitalModule A N]

/-- Evaluation at the actual idempotent lands in the actual fixed subgroup. -/
def toFixed (e : Idempotent A) :
    NonUnitalModuleHom A (Carrier.{uA, uL} e) M →+ FixedPart e M where
  toFun f := ⟨f (generator e), by
    change (e : A) • f (generator e) = f (generator e)
    rw [← f.map_smul, generator_fixed]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem toFixed_val (e : Idempotent A)
    (f : NonUnitalModuleHom A (Carrier.{uA, uL} e) M) :
    (toFixed e f).val = f (generator e) := rfl

/-- The fixed vector gives the original intertwiner `a e ↦ a m`. -/
def fromFixed (e : Idempotent A) (m : FixedPart e M) :
    NonUnitalModuleHom A (Carrier.{uA, uL} e) M where
  toFun x := x.down.val • m.val
  map_zero' := NonUnitalModule.zero_smul m.val
  map_add' x y := NonUnitalModule.add_smul x.down.val y.down.val m.val
  map_smul' a x := mul_smul a x.down.val m.val

@[simp] theorem fromFixed_apply (e : Idempotent A) (m : FixedPart e M)
    (x : Carrier.{uA, uL} e) : fromFixed e m x = x.down.val • m.val := rfl

/-- Evaluation and the orbit formula give the actual additive Hom equivalence. -/
def homEquiv (e : Idempotent A) :
    NonUnitalModuleHom A (Carrier.{uA, uL} e) M ≃+ FixedPart e M where
  toFun := toFixed e
  invFun := fromFixed e
  left_inv f := by
    apply NonUnitalModuleHom.ext
    intro x
    exact (f.map_smul x.down.val (generator e)).symm.trans
      (congrArg f (smul_generator e x))
  right_inv m := Subtype.ext m.property
  map_add' := (toFixed e).map_add

@[simp] theorem homEquiv_apply_val (e : Idempotent A)
    (f : NonUnitalModuleHom A (Carrier.{uA, uL} e) M) :
    (homEquiv e f).val = f (generator e) := rfl

@[simp] theorem homEquiv_symm_apply (e : Idempotent A) (m : FixedPart e M) :
    (homEquiv.{uA, uL, uM} e).symm m = fromFixed e m := rfl

/-- Naturality retains the whole original postcomposition map. -/
theorem homEquiv_naturality (e : Idempotent A) (g : NonUnitalModuleHom A M N) :
    (homEquiv.{uA, uL, uN} e).toAddMonoidHom.comp
        { toFun := fun f => g.comp f
          map_zero' := by ext _x; exact g.map_zero
          map_add' := by intros; ext; exact g.map_add _ _ } =
      (restrict e g).toAddMonoidHom.comp
        (homEquiv.{uA, uL, uM} e).toAddMonoidHom := by
  ext f
  rfl

/-! The complete interface keeps ring, lift and test-carrier universes independent. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (e : Idempotent A) →
    NonUnitalModuleHom A (Carrier.{uA, uL} e) M ≃+ FixedPart e M :=
  @homEquiv.{uA, uL, uM}

end Langlands.Algebra.NonUnitalModuleIdempotentIdeal
