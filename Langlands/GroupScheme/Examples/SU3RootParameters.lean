import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic

/-! # Concrete quadratic root parameters over an involutive commutative ring -/

namespace Langlands.GroupScheme.SU3Root

universe u v w

/-- A ring automorphism with square the identity. -/
structure RingInvolution (A : Type u) [CommRing A] where
  bar : A ≃+* A
  involutive : Function.Involutive bar

variable {A : Type u} {B : Type v} {C : Type w}
  [CommRing A] [CommRing B] [CommRing C]

@[simp] theorem RingInvolution.bar_bar (c : RingInvolution A) (a : A) :
    c.bar (c.bar a) = a := c.involutive a

/-- The concrete coordinate subtype, with the trace-norm equation. -/
def Parameters (c : RingInvolution A) :=
  {p : A × A // p.2 + c.bar p.2 = p.1 * c.bar p.1}

namespace Parameters
variable {c : RingInvolution A} {d : RingInvolution B} {e : RingInvolution C}

/-- The first coordinate. -/
def first (x : Parameters c) : A := x.val.1
/-- The second coordinate. -/
def second (x : Parameters c) : A := x.val.2

@[simp] theorem equation (x : Parameters c) :
    x.second + c.bar x.second = x.first * c.bar x.first := x.property

@[ext] theorem ext {x y : Parameters c} (h₁ : x.first = y.first)
    (h₂ : x.second = y.second) : x = y := Subtype.ext (Prod.ext h₁ h₂)

instance : One (Parameters c) := ⟨⟨(0, 0), by simp⟩⟩
instance : Mul (Parameters c) := ⟨fun x y =>
  ⟨(x.first + y.first, x.second + y.second + x.first * c.bar y.first), by
    simp only [map_add, map_mul, RingInvolution.bar_bar]
    calc
      _ = (x.second + c.bar x.second) + (y.second + c.bar y.second) +
          x.first * c.bar y.first + y.first * c.bar x.first := by ring
      _ = _ := by rw [equation, equation]; ring⟩⟩
instance : Inv (Parameters c) := ⟨fun x => ⟨(-x.first, c.bar x.second), by
  simp only [RingInvolution.bar_bar, map_neg, neg_mul_neg]
  rw [add_comm, equation]⟩⟩

@[simp] theorem first_one : (1 : Parameters c).first = 0 := rfl
@[simp] theorem second_one : (1 : Parameters c).second = 0 := rfl
@[simp] theorem first_mul (x y : Parameters c) : (x * y).first = x.first + y.first := rfl
@[simp] theorem second_mul (x y : Parameters c) :
    (x * y).second = x.second + y.second + x.first * c.bar y.first := rfl
@[simp] theorem first_inv (x : Parameters c) : x⁻¹.first = -x.first := rfl
@[simp] theorem second_inv (x : Parameters c) : x⁻¹.second = c.bar x.second := rfl

instance : Group (Parameters c) where
  mul_assoc x y z := by ext <;> simp [map_add] <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp
    · simp only [second_mul, second_inv, first_inv, second_one]
      linear_combination x.equation

/-- A ring map commuting with the two involutions induces the coordinate group map. -/
def map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    Parameters c →* Parameters d where
  toFun x := ⟨(f x.first, f x.second), by
    change f x.second + d.bar (f x.second) = f x.first * d.bar (f x.first)
    simpa only [map_add, map_mul, hf] using congrArg f x.equation⟩
  map_one' := by
    apply ext <;> change f 0 = 0 <;> exact map_zero f
  map_mul' x y := by
    apply ext
    · change f (x.first + y.first) = f x.first + f y.first
      exact map_add f _ _
    · change f (x.second + y.second + x.first * c.bar y.first) =
        f x.second + f y.second + f x.first * d.bar (f y.first)
      simp only [map_add, map_mul, hf]

@[simp] theorem first_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) (x : Parameters c) :
    (map f hf x).first = f x.first := rfl
@[simp] theorem second_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) (x : Parameters c) :
    (map f hf x).second = f x.second := rfl

@[simp] theorem map_id : map (RingHom.id A) (c := c) (d := c) (fun _ => rfl) =
    MonoidHom.id (Parameters c) := by ext x <;> rfl

theorem map_comp (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (g : B →+* C) (hg : ∀ b, g (d.bar b) = e.bar (g b)) :
    map (g.comp f) (fun a => by simp only [RingHom.comp_apply, hf, hg]) =
      (map g hg).comp (map f hf) := by ext x <;> rfl

/-- An involution-compatible ring equivalence induces a group equivalence. -/
def mapEquiv (f : A ≃+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    Parameters c ≃* Parameters d where
  toFun := map f.toRingHom hf
  invFun := map f.symm.toRingHom (fun b => by
    apply f.injective
    change f (f.symm (d.bar b)) = f (c.bar (f.symm b))
    simp only [hf, RingEquiv.apply_symm_apply])
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' := (map f.toRingHom hf).map_mul

/-- The first coordinate is a homomorphism to the additive group, written multiplicatively. -/
def firstHom (c : RingInvolution A) : Parameters c →* Multiplicative A where
  toFun x := Multiplicative.ofAdd x.first
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The subgroup with first coordinate zero. It is the kernel of `firstHom`. -/
def central (c : RingInvolution A) : Subgroup (Parameters c) := (firstHom c).ker

@[simp] theorem mem_central (x : Parameters c) : x ∈ central c ↔ x.first = 0 := Iff.rfl
@[simp] theorem ker_firstHom : (firstHom c).ker = central c := rfl

/-- All the elements with zero first coordinate commute with every parameter. -/
theorem central_le_center : central c ≤ Subgroup.center (Parameters c) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro x
  have hz' : z.first = 0 := hz
  ext <;> simp [hz', add_comm]

/-- The additive subgroup of trace-zero coordinates. -/
def traceZero (c : RingInvolution A) : AddSubgroup A where
  carrier := {a | a + c.bar a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    linear_combination ha + hb
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_neg] at *
    linear_combination -ha

@[simp] theorem mem_traceZero (a : A) : a ∈ traceZero c ↔ a + c.bar a = 0 := Iff.rfl

/-- Zero-first-coordinate parameters are the multiplicative version of the additive trace kernel. -/
def centralEquivTraceZero (c : RingInvolution A) :
    central c ≃* Multiplicative (traceZero c) where
  toFun x := Multiplicative.ofAdd ⟨x.val.second, by
    simp only [mem_traceZero, x.val.equation, (mem_central _).mp x.property, zero_mul]⟩
  invFun a := ⟨⟨(0, (Multiplicative.toAdd a).val), by
    change (Multiplicative.toAdd a).val + c.bar (Multiplicative.toAdd a).val = 0 * c.bar 0
    rw [zero_mul]
    exact (Multiplicative.toAdd a).property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply ext
    · exact ((mem_central _).mp x.property).symm
    · rfl
  right_inv a := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change x.val.second + y.val.second + x.val.first * c.bar y.val.first =
      x.val.second + y.val.second
    rw [(mem_central _).mp x.property, zero_mul, add_zero]

/-- The commutator convention is `x*y*x⁻¹*y⁻¹`. -/
theorem commutator_coordinates (x y : Parameters c) :
    let z := x * y * x⁻¹ * y⁻¹
    z.first = 0 ∧ z.second = x.first * c.bar y.first - y.first * c.bar x.first := by
  constructor
  · simp
  · simp only [second_mul, first_mul, first_inv, second_inv, map_neg]
    linear_combination x.equation + y.equation

end Parameters
end Langlands.GroupScheme.SU3Root
