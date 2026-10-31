import Langlands.Algebra.NonUnitalModuleAdditive
import Langlands.Algebra.NonUnitalModuleLeftLimit

/-!
# Actual regular-module Hom and its source action

Renard I.1.4–I.1.5, printed p.10/PDF16: actual additive left-linear maps
from the regular module, right-precomposition action, canonical vectors,
and evaluation on actual idempotents.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM

namespace NonUnitalModule

/-- The specified left regular action; this adapter is not a global instance. -/
abbrev regular (A : Type uA) [NonUnitalRing A] : NonUnitalModule A A where
  smul a b := a * b
  smul_zero := mul_zero
  smul_add := mul_add
  mul_smul := mul_assoc
  add_smul := add_mul
  zero_smul := zero_mul

end NonUnitalModule

/-- Actual additive maps from the regular module satisfying the left-linear equation. -/
def regularModuleHomGroup (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    AddSubgroup (A →+ M) where
  carrier := {φ | ∀ a b : A, φ (a * b) = a • φ b}
  zero_mem' := by
    intro a b
    exact (smul_zero a).symm
  add_mem' := by
    intro φ ψ hφ hψ a b
    change φ (a * b) + ψ (a * b) = a • (φ b + ψ b)
    rw [hφ, hψ, smul_add]
  neg_mem' := by
    intro φ hφ a b
    change -φ (a * b) = a • (-φ b)
    rw [hφ, smul_neg]

/-- The actual pointwise additive group `Hom_A(A,M)` for the regular source. -/
abbrev RegularModuleHom (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :=
  ↥(regularModuleHomGroup A M)

namespace RegularModuleHom

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [hM : NonUnitalModule A M]

instance : CoeFun (RegularModuleHom A M) (fun _ => A → M) :=
  ⟨fun φ => φ.val⟩

/-- The inclusion into the actual group of additive maps. -/
def toAddMonoidHom : RegularModuleHom A M →+ (A →+ M) :=
  (regularModuleHomGroup A M).subtype

@[simp] theorem toAddMonoidHom_apply (φ : RegularModuleHom A M) (a : A) :
    toAddMonoidHom φ a = φ a := rfl

@[ext] theorem ext {φ ψ : RegularModuleHom A M} (h : ∀ a, φ a = ψ a) :
    φ = ψ :=
  Subtype.ext (AddMonoidHom.ext h)

@[simp] theorem zero_apply (a : A) : (0 : RegularModuleHom A M) a = 0 := rfl

@[simp] theorem add_apply (φ ψ : RegularModuleHom A M) (a : A) :
    (φ + ψ) a = φ a + ψ a := rfl

@[simp] theorem neg_apply (φ : RegularModuleHom A M) (a : A) :
    (-φ) a = -φ a := rfl

@[simp] theorem map_zero (φ : RegularModuleHom A M) : φ 0 = 0 :=
  φ.val.map_zero

@[simp] theorem map_add (φ : RegularModuleHom A M) (a b : A) :
    φ (a + b) = φ a + φ b :=
  φ.val.map_add a b

/-- The exact regular-source intertwining equation. -/
theorem map_mul_left (φ : RegularModuleHom A M) (a b : A) :
    φ (a * b) = a • φ b :=
  φ.property a b

/-- Comparison with the published original Hom, specifying both actions explicitly. -/
def equivNonUnitalModuleHom :
    RegularModuleHom A M ≃+
      @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM := by
  letI : NonUnitalModule A A := NonUnitalModule.regular A
  exact
    { toFun := fun φ =>
        { toAddMonoidHom := φ.val
          map_smul' := φ.property }
      invFun := fun φ => ⟨φ.toAddMonoidHom, φ.map_smul'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

@[simp] theorem equivNonUnitalModuleHom_apply (φ : RegularModuleHom A M) (a : A) :
    equivNonUnitalModuleHom φ a = φ a := rfl

/-- Right multiplication on the source preserves its left-linear maps. -/
def rightPrecomposition (a : A) : RegularModuleHom A M →+ RegularModuleHom A M where
  toFun φ :=
    ⟨φ.val.comp
      { toFun := fun b => b * a
        map_zero' := zero_mul a
        map_add' b c := add_mul b c a }, by
      intro b c
      change φ ((b * c) * a) = b • φ (c * a)
      rw [mul_assoc, map_mul_left]⟩
  map_zero' := by
    ext b
    rfl
  map_add' φ ψ := by
    ext b
    rfl

@[simp] theorem rightPrecomposition_apply (a : A) (φ : RegularModuleHom A M) (b : A) :
    rightPrecomposition a φ b = φ (b * a) := rfl

/-- The original source formula `(a • φ)(b) = φ(b*a)` with all action laws. -/
instance instNonUnitalModule : NonUnitalModule A (RegularModuleHom A M) where
  smul a φ := rightPrecomposition a φ
  smul_zero a := (rightPrecomposition a).map_zero
  smul_add a := (rightPrecomposition a).map_add
  mul_smul a b φ := by
    ext c
    change φ (c * (a * b)) = φ ((c * a) * b)
    rw [mul_assoc]
  add_smul a b φ := by
    ext c
    change φ (c * (a + b)) = φ (c * a) + φ (c * b)
    rw [mul_add, map_add]
  zero_smul φ := by
    ext b
    change φ (b * 0) = 0
    rw [mul_zero, map_zero]

@[simp] theorem smul_apply (a : A) (φ : RegularModuleHom A M) (b : A) :
    (a • φ) b = φ (b * a) := rfl

/-- An original vector defines its actual regular-source left-linear map. -/
def canonical : NonUnitalModuleHom A M (RegularModuleHom A M) where
  toFun m :=
    ⟨{ toFun := fun a => a • m
       map_zero' := NonUnitalModule.zero_smul m
       map_add' a b := NonUnitalModule.add_smul a b m },
      fun a b => mul_smul a b m⟩
  map_zero' := by
    ext a
    exact smul_zero a
  map_add' m n := by
    ext a
    exact smul_add a m n
  map_smul' a m := by
    ext b
    change b • (a • m) = (b * a) • m
    exact (mul_smul b a m).symm

@[simp] theorem canonical_apply (m : M) (a : A) :
    canonical (A := A) m a = a • m := rfl

/-- Evaluation on actual idempotents is an actual left-compatible additive family. -/
def toLeftLimit : RegularModuleHom A M →+ NonUnitalModuleLeftLimit A M where
  toFun φ := ⟨fun e => φ (e : A), by
    constructor
    · intro e
      exact (φ.map_mul_left (e : A) (e : A)).symm.trans
        (congrArg φ e.property.eq)
    · intro e f h
      exact (φ.map_mul_left (e : A) (f : A)).symm.trans
        (congrArg φ ((Idempotent.le_iff_mul e f).mp h).2)⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    rfl
  map_add' φ ψ := by
    apply Subtype.ext
    funext e
    rfl

@[simp] theorem toLeftLimit_val (φ : RegularModuleHom A M) (e : Idempotent A) :
    (toLeftLimit φ).val e = φ (e : A) := rfl

@[simp] theorem evaluation_toLeftLimit (φ : RegularModuleHom A M) (e : Idempotent A) :
    (NonUnitalModuleLeftLimit.evaluation e (toLeftLimit φ) : M) = φ (e : A) := rfl

/-- The actual evaluation map sends the original vector's Hom to its canonical family. -/
theorem toLeftLimit_comp_canonical :
    (toLeftLimit (A := A) (M := M)).comp canonical.toAddMonoidHom =
      NonUnitalModuleLeftLimit.canonical (A := A) (M := M) := by
  ext m e
  rfl

/-! Complete unapplied interfaces with independent source and target universes. -/

example : (A : Type uA) → [NonUnitalRing A] → NonUnitalModule A A :=
  NonUnitalModule.regular.{uA}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    AddSubgroup (A →+ M) :=
  regularModuleHomGroup.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → (hM : NonUnitalModule A M) →
    RegularModuleHom A M ≃+
      @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM :=
  @equivNonUnitalModuleHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModule A (RegularModuleHom A M) :=
  @instNonUnitalModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleHom A M (RegularModuleHom A M) :=
  @canonical.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    RegularModuleHom A M →+ NonUnitalModuleLeftLimit A M :=
  @toLeftLimit.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → (hM : NonUnitalModule A M) →
    RegularModuleHom A M ≃+
      @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM :=
  @equivNonUnitalModuleHom.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → (hM : NonUnitalModule A M) →
    RegularModuleHom A M ≃+
      @NonUnitalModuleHom A A M _ _ _ (NonUnitalModule.regular A) hM :=
  @equivNonUnitalModuleHom.{1, 0}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleHom A M (RegularModuleHom A M) :=
  @canonical.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleHom A M (RegularModuleHom A M) :=
  @canonical.{1, 0}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    RegularModuleHom A M →+ NonUnitalModuleLeftLimit A M :=
  @toLeftLimit.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    RegularModuleHom A M →+ NonUnitalModuleLeftLimit A M :=
  @toLeftLimit.{1, 0}

/-- Equal carriers retain a specified target action independent of the regular source. -/
example (A : Type uA) [NonUnitalRing A] :
    @RegularModuleHom A A _ _ (NonUnitalModule.zero (A := A) (M := A)) ≃+
      @NonUnitalModuleHom A A A _ _ _ (NonUnitalModule.regular A)
        (NonUnitalModule.zero (A := A) (M := A)) :=
  @equivNonUnitalModuleHom A _ A _ (NonUnitalModule.zero (A := A) (M := A))

end RegularModuleHom
end Langlands.Algebra
