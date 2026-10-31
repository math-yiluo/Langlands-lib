import Langlands.Algebra.IdempotentedRingRightLimitRing
import Langlands.Algebra.IdempotentedRingUniformity
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.UniformSpace.Pi

/-!
# The actual right-linear endomorphism model

Renard I.1.4, printed p.10/PDF16, and I.1.6, printed pp.11-12/PDF17-18.
The ring operations are the actual operations on additive endomorphisms.
The pointwise uniformity uses the original right-annihilator uniformity on A.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace IdempotentedRingEndomorphism

universe uA

variable {A : Type uA} [NonUnitalRing A]

/-- Actual additive endomorphisms commuting with right multiplication. -/
def rightLinearEnd (A : Type uA) [NonUnitalRing A] : Subring (AddMonoid.End A) where
  carrier := {β | ∀ a b : A, β (a * b) = β a * b}
  zero_mem' := by
    intro a b
    exact (zero_mul b).symm
  one_mem' := by
    intro a b
    rfl
  add_mem' := by
    intro β γ hβ hγ a b
    change β (a * b) + γ (a * b) = (β a + γ a) * b
    rw [hβ, hγ, add_mul]
  neg_mem' := by
    intro β hβ a b
    change -β (a * b) = (-β a) * b
    rw [hβ, neg_mul]
  mul_mem' := by
    intro β γ hβ hγ a b
    change β (γ (a * b)) = β (γ a) * b
    rw [hγ, hβ]

@[simp] theorem mem_rightLinearEnd (β : AddMonoid.End A) :
    β ∈ rightLinearEnd A ↔ ∀ a b : A, β (a * b) = β a * b := Iff.rfl

/-- The actual subtype of the right-linear endomorphism subring. -/
abbrev RightLinearEnd (A : Type uA) [NonUnitalRing A] := ↥(rightLinearEnd A)

theorem rightLinearEnd_apply_mul (β : RightLinearEnd A) (a b : A) :
    β.val (a * b) = β.val a * b := β.property a b

/-- Left multiplication, with the original multiplication on A. -/
def leftMultiplication : A →ₙ+* AddMonoid.End A where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext (fun b => zero_mul b)
  map_add' a b := AddMonoidHom.ext (fun c => add_mul a b c)
  map_mul' a b := AddMonoidHom.ext (fun c => mul_assoc a b c)

@[simp] theorem leftMultiplication_apply (a b : A) :
    leftMultiplication a b = a * b := rfl

@[simp] theorem leftMultiplication_toAddMonoidHom :
    (leftMultiplication (A := A)).toAddMonoidHom = AddMonoid.End.mulLeft := rfl

theorem leftMultiplication_coe :
    (leftMultiplication (A := A) : A → AddMonoid.End A) = AddMonoidHom.mulLeft := rfl

/-- Left multiplication as an element of the actual right-linear subring. -/
def leftMultiplicationRight : A →ₙ+* RightLinearEnd A where
  toFun a := ⟨leftMultiplication a, fun b c => (mul_assoc a b c).symm⟩
  map_zero' := Subtype.ext (map_zero leftMultiplication)
  map_add' a b := Subtype.ext (map_add leftMultiplication a b)
  map_mul' a b := Subtype.ext (map_mul leftMultiplication a b)

@[simp] theorem leftMultiplicationRight_val (a : A) :
    (leftMultiplicationRight a).val = leftMultiplication a := rfl

@[simp] theorem leftMultiplicationRight_apply (a b : A) :
    (leftMultiplicationRight a).val b = a * b := rfl

/-- The actual full nonunital ring map is retained under subtype inclusion. -/
theorem leftMultiplicationRight_subtype_comp :
    (rightLinearEnd A).subtype.toNonUnitalRingHom.comp leftMultiplicationRight =
      leftMultiplication (A := A) := rfl

theorem leftMultiplicationRight_coe :
    (fun a : A => (leftMultiplicationRight a).val) =
      (leftMultiplication (A := A) : A → AddMonoid.End A) := rfl

/-- Internal evaluation of a right-compatible family as an additive endomorphism. -/
def toEnd (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) : AddMonoid.End A where
  toFun := IdempotentedRingRightLimit.applyOriginal hA x
  map_zero' := IdempotentedRingRightLimit.applyOriginal_zero hA x
  map_add' := IdempotentedRingRightLimit.applyOriginal_add hA x

@[simp] theorem toEnd_apply (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) :
    toEnd hA x a = IdempotentedRingRightLimit.applyOriginal hA x a := rfl

theorem toEnd_coe (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) :
    (toEnd hA x : A → A) = IdempotentedRingRightLimit.applyOriginal hA x := rfl

/-- The specified published family ring maps into actual additive endomorphisms. -/
def toEndRingHom (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* AddMonoid.End A := by
  letI := IdempotentedRingRightLimit.ring hA
  exact
    { toFun := toEnd hA
      map_zero' := AddMonoidHom.ext (IdempotentedRingRightLimit.zero_applyOriginal hA)
      map_one' := AddMonoidHom.ext (IdempotentedRingRightLimit.unit_applyOriginal hA)
      map_add' := fun x y => AddMonoidHom.ext
        (IdempotentedRingRightLimit.add_applyOriginal hA x y)
      map_mul' := fun x y => AddMonoidHom.ext
        (IdempotentedRingRightLimit.product_applyOriginal hA x y) }

@[simp] theorem toEndRingHom_apply (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) : toEndRingHom hA x = toEnd hA x := rfl

theorem toEndRingHom_coe (hA : IsIdempotented A) :
    (toEndRingHom hA : IdempotentedRingRightLimit A → AddMonoid.End A) = toEnd hA := rfl

/-- The same actual ring map, factored into the concrete right-linear subring. -/
def toRightLinearEnd (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* RightLinearEnd A := by
  letI := IdempotentedRingRightLimit.ring hA
  exact (toEndRingHom hA).codRestrict (rightLinearEnd A)
    (fun x => IdempotentedRingRightLimit.applyOriginal_mul hA x)

@[simp] theorem toRightLinearEnd_val (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) :
    (toRightLinearEnd hA x).val = toEndRingHom hA x := rfl

@[simp] theorem toRightLinearEnd_apply (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) :
    (toRightLinearEnd hA x).val a =
      IdempotentedRingRightLimit.applyOriginal hA x a := rfl

/-- Equality of the entire bundled ring map after actual subtype inclusion. -/
theorem toRightLinearEnd_subtype_comp (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    (rightLinearEnd A).subtype.comp (toRightLinearEnd hA) = toEndRingHom hA := rfl

theorem toRightLinearEnd_coe (hA : IsIdempotented A) :
    (fun x : IdempotentedRingRightLimit A => (toRightLinearEnd hA x).val) =
      toEnd hA := rfl

/-- Every left local unit computes the actual endomorphism's value. -/
theorem toEndRingHom_apply_eq (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (he : (e : A) * a = a) :
    toEndRingHom hA x a = x.val e * a :=
  IdempotentedRingRightLimit.applyOriginal_eq hA x a e he

@[simp] theorem toEndRingHom_idempotent (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A) :
    toEndRingHom hA x (e : A) = x.val e :=
  IdempotentedRingRightLimit.applyOriginal_idempotent hA x e

theorem toRightLinearEnd_apply_eq (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (he : (e : A) * a = a) :
    (toRightLinearEnd hA x).val a = x.val e * a :=
  toEndRingHom_apply_eq hA x a e he

@[simp] theorem toRightLinearEnd_idempotent (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A) :
    (toRightLinearEnd hA x).val (e : A) = x.val e :=
  toEndRingHom_idempotent hA x e

@[simp] theorem toEndRingHom_canonical (hA : IsIdempotented A) (a : A) :
    toEndRingHom hA (IdempotentedRingRightLimit.canonical a) = leftMultiplication a := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimit.canonical_applyOriginal hA a

@[simp] theorem toRightLinearEnd_canonical (hA : IsIdempotented A) (a : A) :
    toRightLinearEnd hA (IdempotentedRingRightLimit.canonical a) =
      leftMultiplicationRight a :=
  Subtype.ext (toEndRingHom_canonical hA a)

/-- Evaluating a right-linear endomorphism at idempotents gives an actual
right-compatible family; this construction needs no local-unit assumption. -/
def idempotentEvaluation : RightLinearEnd A →+ IdempotentedRingRightLimit A where
  toFun β := ⟨fun e => β.val (e : A), by
    constructor
    · intro e
      rw [← β.property, e.property.eq]
    · intro e f hef
      rw [← β.property, ((Idempotent.le_iff_mul e f).mp hef).1]⟩
  map_zero' := by
    apply Subtype.ext
    funext e
    rfl
  map_add' β γ := by
    apply Subtype.ext
    funext e
    rfl

@[simp] theorem idempotentEvaluation_val (β : RightLinearEnd A) (e : Idempotent A) :
    (idempotentEvaluation β).val e = β.val (e : A) := rfl

theorem idempotentEvaluation_coe :
    (fun β : RightLinearEnd A => (idempotentEvaluation β).val) =
      (fun (β : RightLinearEnd A) (e : Idempotent A) => β.val (e : A)) := rfl

/-- The function product uses exactly the original right-annihilator uniformity
in every value coordinate. It is deliberately not a global instance. -/
@[instance_reducible]
def functionUniformSpace (A : Type uA) [NonUnitalRing A] : UniformSpace (A → A) :=
  @Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)

/-- Pointwise convergence of actual additive endomorphisms, with the original
right-annihilator uniformity on values. -/
@[instance_reducible]
def pointwiseUniformSpace (A : Type uA) [NonUnitalRing A] : UniformSpace (AddMonoid.End A) :=
  UniformSpace.comap (fun β : AddMonoid.End A => (β : A → A)) (functionUniformSpace A)

/-- The specified restriction through the actual right-linear subtype. -/
@[instance_reducible]
def rightLinearEndUniformSpace (A : Type uA) [NonUnitalRing A] :
    UniformSpace (RightLinearEnd A) :=
  UniformSpace.comap (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A)

theorem pointwiseUniformSpace_eq_comap :
    pointwiseUniformSpace A = UniformSpace.comap
      (fun β : AddMonoid.End A => (β : A → A))
      (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) := rfl

theorem rightLinearEndUniformSpace_eq_comap :
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A) := rfl

theorem rightLinearEndUniformSpace_eq_function_comap :
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => (β.val : A → A)) (functionUniformSpace A) :=
  UniformSpace.comap_comap.symm

theorem pointwise_toTopologicalSpace :
    (pointwiseUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : AddMonoid.End A => (β : A → A)) (functionUniformSpace A).toTopologicalSpace := rfl

theorem rightLinearEnd_toTopologicalSpace :
    (rightLinearEndUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A).toTopologicalSpace := rfl

theorem uniformContinuous_toFunction :
    @UniformContinuous (AddMonoid.End A) (A → A)
      (pointwiseUniformSpace A) (functionUniformSpace A)
      (fun β : AddMonoid.End A => (β : A → A)) :=
  @uniformContinuous_comap _ _ _ (functionUniformSpace A)

theorem uniformContinuous_subtype :
    @UniformContinuous (RightLinearEnd A) (AddMonoid.End A)
      (rightLinearEndUniformSpace A) (pointwiseUniformSpace A)
      (fun β : RightLinearEnd A => β.val) :=
  @uniformContinuous_comap _ _ _ (pointwiseUniformSpace A)

theorem uniformContinuous_evaluation (a : A) :
    @UniformContinuous (AddMonoid.End A) A
      (pointwiseUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : AddMonoid.End A => β a) := by
  let : UniformSpace A := idempotentedRingUniformSpace A
  let : UniformSpace (AddMonoid.End A) := pointwiseUniformSpace A
  exact (Pi.uniformContinuous_proj (fun _ : A => A) a).comp uniformContinuous_toFunction

theorem uniformContinuous_rightLinearEvaluation (a : A) :
    @UniformContinuous (RightLinearEnd A) A
      (rightLinearEndUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : RightLinearEnd A => β.val a) := by
  let : UniformSpace A := idempotentedRingUniformSpace A
  let : UniformSpace (AddMonoid.End A) := pointwiseUniformSpace A
  let : UniformSpace (RightLinearEnd A) := rightLinearEndUniformSpace A
  exact (uniformContinuous_evaluation a).comp uniformContinuous_subtype

/-! Complete unapplied declaration checks, including both small universe levels. -/

section ArbitraryUniverse

example : ∀ (A : Type uA) [NonUnitalRing A], Subring (AddMonoid.End A) :=
  @rightLinearEnd

example : ∀ (A : Type uA) [NonUnitalRing A], Type uA :=
  @RightLinearEnd

example : ∀ {A : Type uA} [NonUnitalRing A], A →ₙ+* AddMonoid.End A :=
  @leftMultiplication

example : ∀ {A : Type uA} [NonUnitalRing A], A →ₙ+* RightLinearEnd A :=
  @leftMultiplicationRight

example : ∀ {A : Type uA} [NonUnitalRing A],
    IsIdempotented A → IdempotentedRingRightLimit A → AddMonoid.End A :=
  @toEnd

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* AddMonoid.End A :=
  @toEndRingHom

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* RightLinearEnd A :=
  @toRightLinearEnd

example : ∀ {A : Type uA} [NonUnitalRing A],
    RightLinearEnd A →+ IdempotentedRingRightLimit A :=
  @idempotentEvaluation

example : ∀ (A : Type uA) [NonUnitalRing A], UniformSpace (A → A) :=
  @functionUniformSpace

example : ∀ (A : Type uA) [NonUnitalRing A], UniformSpace (AddMonoid.End A) :=
  @pointwiseUniformSpace

example : ∀ (A : Type uA) [NonUnitalRing A], UniformSpace (RightLinearEnd A) :=
  @rightLinearEndUniformSpace

example : ∀ {A : Type uA} [NonUnitalRing A] (a b : A),
    leftMultiplication a b = a * b :=
  @leftMultiplication_apply

example : ∀ {A : Type uA} [NonUnitalRing A],
    (leftMultiplication (A := A)).toAddMonoidHom = AddMonoid.End.mulLeft :=
  @leftMultiplication_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (a : A),
    (leftMultiplicationRight a).val = leftMultiplication a :=
  @leftMultiplicationRight_val

example : ∀ {A : Type uA} [NonUnitalRing A] (a b : A),
    (leftMultiplicationRight a).val b = a * b :=
  @leftMultiplicationRight_apply

example : ∀ {A : Type uA} [NonUnitalRing A],
    (rightLinearEnd A).subtype.toNonUnitalRingHom.comp leftMultiplicationRight =
      leftMultiplication (A := A) :=
  @leftMultiplicationRight_subtype_comp

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A),
    toEnd hA x a = IdempotentedRingRightLimit.applyOriginal hA x a :=
  @toEnd_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A),
    (toEnd hA x : A → A) = IdempotentedRingRightLimit.applyOriginal hA x :=
  @toEnd_coe

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (toEndRingHom hA : IdempotentedRingRightLimit A → AddMonoid.End A) = toEnd hA :=
  @toEndRingHom_coe

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A), toEndRingHom hA x = toEnd hA x :=
  @toEndRingHom_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A),
    (toRightLinearEnd hA x).val = toEndRingHom hA x :=
  @toRightLinearEnd_val

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A),
    (toRightLinearEnd hA x).val a = IdempotentedRingRightLimit.applyOriginal hA x a :=
  @toRightLinearEnd_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    (rightLinearEnd A).subtype.comp (toRightLinearEnd hA) = toEndRingHom hA :=
  @toRightLinearEnd_subtype_comp

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (_he : (e : A) * a = a), toEndRingHom hA x a = x.val e * a :=
  @toEndRingHom_apply_eq

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    toEndRingHom hA x (e : A) = x.val e :=
  @toEndRingHom_idempotent

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (a : A),
    toEndRingHom hA (IdempotentedRingRightLimit.canonical a) = leftMultiplication a :=
  @toEndRingHom_canonical

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (_he : (e : A) * a = a), (toRightLinearEnd hA x).val a = x.val e * a :=
  @toRightLinearEnd_apply_eq

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    (toRightLinearEnd hA x).val (e : A) = x.val e :=
  @toRightLinearEnd_idempotent

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (a : A),
    toRightLinearEnd hA (IdempotentedRingRightLimit.canonical a) =
      leftMultiplicationRight a :=
  @toRightLinearEnd_canonical

example : ∀ {A : Type uA} [NonUnitalRing A] (β : RightLinearEnd A) (e : Idempotent A),
    (idempotentEvaluation β).val e = β.val (e : A) :=
  @idempotentEvaluation_val

example : ∀ {A : Type uA} [NonUnitalRing A],
    pointwiseUniformSpace A = UniformSpace.comap
      (fun β : AddMonoid.End A => (β : A → A))
      (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) :=
  @pointwiseUniformSpace_eq_comap

example : ∀ {A : Type uA} [NonUnitalRing A],
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_comap

example : ∀ {A : Type uA} [NonUnitalRing A],
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => (β.val : A → A)) (functionUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_function_comap

example : ∀ {A : Type uA} [NonUnitalRing A],
    (pointwiseUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : AddMonoid.End A => (β : A → A)) (functionUniformSpace A).toTopologicalSpace :=
  @pointwise_toTopologicalSpace

example : ∀ {A : Type uA} [NonUnitalRing A],
    (rightLinearEndUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A).toTopologicalSpace :=
  @rightLinearEnd_toTopologicalSpace

example : ∀ {A : Type uA} [NonUnitalRing A],
    @UniformContinuous (AddMonoid.End A) (A → A)
      (pointwiseUniformSpace A) (functionUniformSpace A)
      (fun β : AddMonoid.End A => (β : A → A)) :=
  @uniformContinuous_toFunction

example : ∀ {A : Type uA} [NonUnitalRing A],
    @UniformContinuous (RightLinearEnd A) (AddMonoid.End A)
      (rightLinearEndUniformSpace A) (pointwiseUniformSpace A)
      (fun β : RightLinearEnd A => β.val) :=
  @uniformContinuous_subtype

example : ∀ {A : Type uA} [NonUnitalRing A] (a : A),
    @UniformContinuous (AddMonoid.End A) A
      (pointwiseUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : AddMonoid.End A => β a) :=
  @uniformContinuous_evaluation

example : ∀ {A : Type uA} [NonUnitalRing A] (a : A),
    @UniformContinuous (RightLinearEnd A) A
      (rightLinearEndUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : RightLinearEnd A => β.val a) :=
  @uniformContinuous_rightLinearEvaluation

example : ∀ {A : Type uA} [NonUnitalRing A],
    (leftMultiplication (A := A) : A → AddMonoid.End A) = AddMonoidHom.mulLeft :=
  @leftMultiplication_coe

example : ∀ {A : Type uA} [NonUnitalRing A],
    (fun a : A => (leftMultiplicationRight a).val) =
      (leftMultiplication (A := A) : A → AddMonoid.End A) :=
  @leftMultiplicationRight_coe

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A),
    (fun x : IdempotentedRingRightLimit A => (toRightLinearEnd hA x).val) =
      toEnd hA :=
  @toRightLinearEnd_coe

example : ∀ {A : Type uA} [NonUnitalRing A],
    (fun β : RightLinearEnd A => (idempotentEvaluation β).val) =
      (fun (β : RightLinearEnd A) (e : Idempotent A) => β.val (e : A)) :=
  @idempotentEvaluation_coe

end ArbitraryUniverse

section UniverseZero

example : ∀ (A : Type 0) [NonUnitalRing A], Subring (AddMonoid.End A) :=
  @rightLinearEnd

example : ∀ (A : Type 0) [NonUnitalRing A], Type 0 :=
  @RightLinearEnd

example : ∀ {A : Type 0} [NonUnitalRing A], A →ₙ+* AddMonoid.End A :=
  @leftMultiplication

example : ∀ {A : Type 0} [NonUnitalRing A], A →ₙ+* RightLinearEnd A :=
  @leftMultiplicationRight

example : ∀ {A : Type 0} [NonUnitalRing A],
    IsIdempotented A → IdempotentedRingRightLimit A → AddMonoid.End A :=
  @toEnd

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* AddMonoid.End A :=
  @toEndRingHom

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* RightLinearEnd A :=
  @toRightLinearEnd

example : ∀ {A : Type 0} [NonUnitalRing A],
    RightLinearEnd A →+ IdempotentedRingRightLimit A :=
  @idempotentEvaluation

example : ∀ (A : Type 0) [NonUnitalRing A], UniformSpace (A → A) :=
  @functionUniformSpace

example : ∀ (A : Type 0) [NonUnitalRing A], UniformSpace (AddMonoid.End A) :=
  @pointwiseUniformSpace

example : ∀ (A : Type 0) [NonUnitalRing A], UniformSpace (RightLinearEnd A) :=
  @rightLinearEndUniformSpace

example : ∀ {A : Type 0} [NonUnitalRing A] (a b : A),
    leftMultiplication a b = a * b :=
  @leftMultiplication_apply

example : ∀ {A : Type 0} [NonUnitalRing A],
    (leftMultiplication (A := A)).toAddMonoidHom = AddMonoid.End.mulLeft :=
  @leftMultiplication_toAddMonoidHom

example : ∀ {A : Type 0} [NonUnitalRing A] (a : A),
    (leftMultiplicationRight a).val = leftMultiplication a :=
  @leftMultiplicationRight_val

example : ∀ {A : Type 0} [NonUnitalRing A] (a b : A),
    (leftMultiplicationRight a).val b = a * b :=
  @leftMultiplicationRight_apply

example : ∀ {A : Type 0} [NonUnitalRing A],
    (rightLinearEnd A).subtype.toNonUnitalRingHom.comp leftMultiplicationRight =
      leftMultiplication (A := A) :=
  @leftMultiplicationRight_subtype_comp

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A),
    toEnd hA x a = IdempotentedRingRightLimit.applyOriginal hA x a :=
  @toEnd_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A),
    (toEnd hA x : A → A) = IdempotentedRingRightLimit.applyOriginal hA x :=
  @toEnd_coe

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (toEndRingHom hA : IdempotentedRingRightLimit A → AddMonoid.End A) = toEnd hA :=
  @toEndRingHom_coe

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A), toEndRingHom hA x = toEnd hA x :=
  @toEndRingHom_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A),
    (toRightLinearEnd hA x).val = toEndRingHom hA x :=
  @toRightLinearEnd_val

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A),
    (toRightLinearEnd hA x).val a = IdempotentedRingRightLimit.applyOriginal hA x a :=
  @toRightLinearEnd_apply

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    (rightLinearEnd A).subtype.comp (toRightLinearEnd hA) = toEndRingHom hA :=
  @toRightLinearEnd_subtype_comp

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (_he : (e : A) * a = a), toEndRingHom hA x a = x.val e * a :=
  @toEndRingHom_apply_eq

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    toEndRingHom hA x (e : A) = x.val e :=
  @toEndRingHom_idempotent

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (a : A),
    toEndRingHom hA (IdempotentedRingRightLimit.canonical a) = leftMultiplication a :=
  @toEndRingHom_canonical

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (_he : (e : A) * a = a), (toRightLinearEnd hA x).val a = x.val e * a :=
  @toRightLinearEnd_apply_eq

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    (toRightLinearEnd hA x).val (e : A) = x.val e :=
  @toRightLinearEnd_idempotent

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (a : A),
    toRightLinearEnd hA (IdempotentedRingRightLimit.canonical a) =
      leftMultiplicationRight a :=
  @toRightLinearEnd_canonical

example : ∀ {A : Type 0} [NonUnitalRing A] (β : RightLinearEnd A) (e : Idempotent A),
    (idempotentEvaluation β).val e = β.val (e : A) :=
  @idempotentEvaluation_val

example : ∀ {A : Type 0} [NonUnitalRing A],
    pointwiseUniformSpace A = UniformSpace.comap
      (fun β : AddMonoid.End A => (β : A → A))
      (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) :=
  @pointwiseUniformSpace_eq_comap

example : ∀ {A : Type 0} [NonUnitalRing A],
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_comap

example : ∀ {A : Type 0} [NonUnitalRing A],
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => (β.val : A → A)) (functionUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_function_comap

example : ∀ {A : Type 0} [NonUnitalRing A],
    (pointwiseUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : AddMonoid.End A => (β : A → A)) (functionUniformSpace A).toTopologicalSpace :=
  @pointwise_toTopologicalSpace

example : ∀ {A : Type 0} [NonUnitalRing A],
    (rightLinearEndUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A).toTopologicalSpace :=
  @rightLinearEnd_toTopologicalSpace

example : ∀ {A : Type 0} [NonUnitalRing A],
    @UniformContinuous (AddMonoid.End A) (A → A)
      (pointwiseUniformSpace A) (functionUniformSpace A)
      (fun β : AddMonoid.End A => (β : A → A)) :=
  @uniformContinuous_toFunction

example : ∀ {A : Type 0} [NonUnitalRing A],
    @UniformContinuous (RightLinearEnd A) (AddMonoid.End A)
      (rightLinearEndUniformSpace A) (pointwiseUniformSpace A)
      (fun β : RightLinearEnd A => β.val) :=
  @uniformContinuous_subtype

example : ∀ {A : Type 0} [NonUnitalRing A] (a : A),
    @UniformContinuous (AddMonoid.End A) A
      (pointwiseUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : AddMonoid.End A => β a) :=
  @uniformContinuous_evaluation

example : ∀ {A : Type 0} [NonUnitalRing A] (a : A),
    @UniformContinuous (RightLinearEnd A) A
      (rightLinearEndUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : RightLinearEnd A => β.val a) :=
  @uniformContinuous_rightLinearEvaluation

example : ∀ {A : Type 0} [NonUnitalRing A],
    (leftMultiplication (A := A) : A → AddMonoid.End A) = AddMonoidHom.mulLeft :=
  @leftMultiplication_coe

example : ∀ {A : Type 0} [NonUnitalRing A],
    (fun a : A => (leftMultiplicationRight a).val) =
      (leftMultiplication (A := A) : A → AddMonoid.End A) :=
  @leftMultiplicationRight_coe

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A),
    (fun x : IdempotentedRingRightLimit A => (toRightLinearEnd hA x).val) =
      toEnd hA :=
  @toRightLinearEnd_coe

example : ∀ {A : Type 0} [NonUnitalRing A],
    (fun β : RightLinearEnd A => (idempotentEvaluation β).val) =
      (fun (β : RightLinearEnd A) (e : Idempotent A) => β.val (e : A)) :=
  @idempotentEvaluation_coe

end UniverseZero

section UniverseOne

example : ∀ (A : Type 1) [NonUnitalRing A], Subring (AddMonoid.End A) :=
  @rightLinearEnd

example : ∀ (A : Type 1) [NonUnitalRing A], Type 1 :=
  @RightLinearEnd

example : ∀ {A : Type 1} [NonUnitalRing A], A →ₙ+* AddMonoid.End A :=
  @leftMultiplication

example : ∀ {A : Type 1} [NonUnitalRing A], A →ₙ+* RightLinearEnd A :=
  @leftMultiplicationRight

example : ∀ {A : Type 1} [NonUnitalRing A],
    IsIdempotented A → IdempotentedRingRightLimit A → AddMonoid.End A :=
  @toEnd

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* AddMonoid.End A :=
  @toEndRingHom

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* RightLinearEnd A :=
  @toRightLinearEnd

example : ∀ {A : Type 1} [NonUnitalRing A],
    RightLinearEnd A →+ IdempotentedRingRightLimit A :=
  @idempotentEvaluation

example : ∀ (A : Type 1) [NonUnitalRing A], UniformSpace (A → A) :=
  @functionUniformSpace

example : ∀ (A : Type 1) [NonUnitalRing A], UniformSpace (AddMonoid.End A) :=
  @pointwiseUniformSpace

example : ∀ (A : Type 1) [NonUnitalRing A], UniformSpace (RightLinearEnd A) :=
  @rightLinearEndUniformSpace

example : ∀ {A : Type 1} [NonUnitalRing A] (a b : A),
    leftMultiplication a b = a * b :=
  @leftMultiplication_apply

example : ∀ {A : Type 1} [NonUnitalRing A],
    (leftMultiplication (A := A)).toAddMonoidHom = AddMonoid.End.mulLeft :=
  @leftMultiplication_toAddMonoidHom

example : ∀ {A : Type 1} [NonUnitalRing A] (a : A),
    (leftMultiplicationRight a).val = leftMultiplication a :=
  @leftMultiplicationRight_val

example : ∀ {A : Type 1} [NonUnitalRing A] (a b : A),
    (leftMultiplicationRight a).val b = a * b :=
  @leftMultiplicationRight_apply

example : ∀ {A : Type 1} [NonUnitalRing A],
    (rightLinearEnd A).subtype.toNonUnitalRingHom.comp leftMultiplicationRight =
      leftMultiplication (A := A) :=
  @leftMultiplicationRight_subtype_comp

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A),
    toEnd hA x a = IdempotentedRingRightLimit.applyOriginal hA x a :=
  @toEnd_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A),
    (toEnd hA x : A → A) = IdempotentedRingRightLimit.applyOriginal hA x :=
  @toEnd_coe

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (toEndRingHom hA : IdempotentedRingRightLimit A → AddMonoid.End A) = toEnd hA :=
  @toEndRingHom_coe

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A), toEndRingHom hA x = toEnd hA x :=
  @toEndRingHom_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A),
    (toRightLinearEnd hA x).val = toEndRingHom hA x :=
  @toRightLinearEnd_val

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A),
    (toRightLinearEnd hA x).val a = IdempotentedRingRightLimit.applyOriginal hA x a :=
  @toRightLinearEnd_apply

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    (rightLinearEnd A).subtype.comp (toRightLinearEnd hA) = toEndRingHom hA :=
  @toRightLinearEnd_subtype_comp

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (_he : (e : A) * a = a), toEndRingHom hA x a = x.val e * a :=
  @toEndRingHom_apply_eq

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    toEndRingHom hA x (e : A) = x.val e :=
  @toEndRingHom_idempotent

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (a : A),
    toEndRingHom hA (IdempotentedRingRightLimit.canonical a) = leftMultiplication a :=
  @toEndRingHom_canonical

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (a : A) (e : Idempotent A)
    (_he : (e : A) * a = a), (toRightLinearEnd hA x).val a = x.val e * a :=
  @toRightLinearEnd_apply_eq

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (e : Idempotent A),
    (toRightLinearEnd hA x).val (e : A) = x.val e :=
  @toRightLinearEnd_idempotent

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (a : A),
    toRightLinearEnd hA (IdempotentedRingRightLimit.canonical a) =
      leftMultiplicationRight a :=
  @toRightLinearEnd_canonical

example : ∀ {A : Type 1} [NonUnitalRing A] (β : RightLinearEnd A) (e : Idempotent A),
    (idempotentEvaluation β).val e = β.val (e : A) :=
  @idempotentEvaluation_val

example : ∀ {A : Type 1} [NonUnitalRing A],
    pointwiseUniformSpace A = UniformSpace.comap
      (fun β : AddMonoid.End A => (β : A → A))
      (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) :=
  @pointwiseUniformSpace_eq_comap

example : ∀ {A : Type 1} [NonUnitalRing A],
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_comap

example : ∀ {A : Type 1} [NonUnitalRing A],
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => (β.val : A → A)) (functionUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_function_comap

example : ∀ {A : Type 1} [NonUnitalRing A],
    (pointwiseUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : AddMonoid.End A => (β : A → A)) (functionUniformSpace A).toTopologicalSpace :=
  @pointwise_toTopologicalSpace

example : ∀ {A : Type 1} [NonUnitalRing A],
    (rightLinearEndUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A).toTopologicalSpace :=
  @rightLinearEnd_toTopologicalSpace

example : ∀ {A : Type 1} [NonUnitalRing A],
    @UniformContinuous (AddMonoid.End A) (A → A)
      (pointwiseUniformSpace A) (functionUniformSpace A)
      (fun β : AddMonoid.End A => (β : A → A)) :=
  @uniformContinuous_toFunction

example : ∀ {A : Type 1} [NonUnitalRing A],
    @UniformContinuous (RightLinearEnd A) (AddMonoid.End A)
      (rightLinearEndUniformSpace A) (pointwiseUniformSpace A)
      (fun β : RightLinearEnd A => β.val) :=
  @uniformContinuous_subtype

example : ∀ {A : Type 1} [NonUnitalRing A] (a : A),
    @UniformContinuous (AddMonoid.End A) A
      (pointwiseUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : AddMonoid.End A => β a) :=
  @uniformContinuous_evaluation

example : ∀ {A : Type 1} [NonUnitalRing A] (a : A),
    @UniformContinuous (RightLinearEnd A) A
      (rightLinearEndUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : RightLinearEnd A => β.val a) :=
  @uniformContinuous_rightLinearEvaluation

example : ∀ {A : Type 1} [NonUnitalRing A],
    (leftMultiplication (A := A) : A → AddMonoid.End A) = AddMonoidHom.mulLeft :=
  @leftMultiplication_coe

example : ∀ {A : Type 1} [NonUnitalRing A],
    (fun a : A => (leftMultiplicationRight a).val) =
      (leftMultiplication (A := A) : A → AddMonoid.End A) :=
  @leftMultiplicationRight_coe

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A),
    (fun x : IdempotentedRingRightLimit A => (toRightLinearEnd hA x).val) =
      toEnd hA :=
  @toRightLinearEnd_coe

example : ∀ {A : Type 1} [NonUnitalRing A],
    (fun β : RightLinearEnd A => (idempotentEvaluation β).val) =
      (fun (β : RightLinearEnd A) (e : Idempotent A) => β.val (e : A)) :=
  @idempotentEvaluation_coe

end UniverseOne

/-! Competing structures cannot replace any of the specified constructions. -/
section CompetingStructures

variable [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]
  [competingValueUniformity : UniformSpace A]
  [competingFunctionUniformity : UniformSpace (A → A)]
  [competingEndUniformity : UniformSpace (AddMonoid.End A)]
  [competingSubringUniformity : UniformSpace (RightLinearEnd A)]

example : ∀ (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* AddMonoid.End A :=
  @toEndRingHom A _

example : ∀ (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    IdempotentedRingRightLimit A →+* RightLinearEnd A :=
  @toRightLinearEnd A _

example : ∀ (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    (rightLinearEnd A).subtype.comp (toRightLinearEnd hA) = toEndRingHom hA :=
  @toRightLinearEnd_subtype_comp A _

example : ∀ (hA : IsIdempotented A),
    (toEndRingHom hA : IdempotentedRingRightLimit A → AddMonoid.End A) = toEnd hA :=
  @toEndRingHom_coe A _

example : ∀ (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A)
    (a : A) (e : Idempotent A) (_he : (e : A) * a = a),
    (toRightLinearEnd hA x).val a = x.val e * a :=
  @toRightLinearEnd_apply_eq A _

example : ∀ (hA : IsIdempotented A) (a : A),
    toRightLinearEnd hA (IdempotentedRingRightLimit.canonical a) =
      leftMultiplicationRight a :=
  @toRightLinearEnd_canonical A _

example : ∀ (β : RightLinearEnd A) (e : Idempotent A),
    (idempotentEvaluation β).val e = β.val (e : A) :=
  @idempotentEvaluation_val A _

example :
    pointwiseUniformSpace A = UniformSpace.comap
      (fun β : AddMonoid.End A => (β : A → A))
      (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) :=
  @pointwiseUniformSpace_eq_comap A _

example :
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_comap A _

example :
    rightLinearEndUniformSpace A = UniformSpace.comap
      (fun β : RightLinearEnd A => (β.val : A → A)) (functionUniformSpace A) :=
  @rightLinearEndUniformSpace_eq_function_comap A _

example :
    (pointwiseUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : AddMonoid.End A => (β : A → A)) (functionUniformSpace A).toTopologicalSpace :=
  @pointwise_toTopologicalSpace A _

example :
    (rightLinearEndUniformSpace A).toTopologicalSpace = TopologicalSpace.induced
      (fun β : RightLinearEnd A => β.val) (pointwiseUniformSpace A).toTopologicalSpace :=
  @rightLinearEnd_toTopologicalSpace A _

example :
    @UniformContinuous (AddMonoid.End A) (A → A)
      (pointwiseUniformSpace A) (functionUniformSpace A)
      (fun β : AddMonoid.End A => (β : A → A)) :=
  @uniformContinuous_toFunction A _

example :
    @UniformContinuous (RightLinearEnd A) (AddMonoid.End A)
      (rightLinearEndUniformSpace A) (pointwiseUniformSpace A)
      (fun β : RightLinearEnd A => β.val) :=
  @uniformContinuous_subtype A _

example : ∀ (a : A),
    @UniformContinuous (AddMonoid.End A) A
      (pointwiseUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : AddMonoid.End A => β a) :=
  @uniformContinuous_evaluation A _

example : ∀ (a : A),
    @UniformContinuous (RightLinearEnd A) A
      (rightLinearEndUniformSpace A) (idempotentedRingUniformSpace A)
      (fun β : RightLinearEnd A => β.val a) :=
  @uniformContinuous_rightLinearEvaluation A _

example :
    (fun a : A => (leftMultiplicationRight a).val) =
      (leftMultiplication (A := A) : A → AddMonoid.End A) :=
  @leftMultiplicationRight_coe A _

example : ∀ (hA : IsIdempotented A),
    (fun x : IdempotentedRingRightLimit A => (toRightLinearEnd hA x).val) =
      toEnd hA :=
  @toRightLinearEnd_coe A _

example :
    (fun β : RightLinearEnd A => (idempotentEvaluation β).val) =
      (fun (β : RightLinearEnd A) (e : Idempotent A) => β.val (e : A)) :=
  @idempotentEvaluation_coe A _

end CompetingStructures

/-! Zero rings are allowed with only the original nonunital operations. -/
section ZeroRing

variable [Subsingleton A]

example : ∃ hA : IsIdempotented A, ∀ x : IdempotentedRingRightLimit A,
    toEndRingHom hA x = 0 ∧ toRightLinearEnd hA x = 0 := by
  have hA : IsIdempotented A := by
    intro s
    refine ⟨⟨0, zero_mul 0⟩, ?_⟩
    intro a _ha
    exact Subsingleton.elim _ _
  refine ⟨hA, ?_⟩
  intro x
  constructor
  · apply AddMonoidHom.ext
    intro a
    exact Subsingleton.elim _ _
  · apply Subtype.ext
    apply AddMonoidHom.ext
    intro a
    exact Subsingleton.elim _ _

example (β : RightLinearEnd A) : idempotentEvaluation β = 0 := by
  apply Subtype.ext
  funext e
  exact Subsingleton.elim _ _

example (a : A) : leftMultiplicationRight a = 0 := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro b
  exact Subsingleton.elim _ _

end ZeroRing

end IdempotentedRingEndomorphism
end Langlands.Algebra
