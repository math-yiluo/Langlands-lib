import Langlands.Algebra.CompatibleUnitization
import Langlands.Algebra.NonUnitalModuleTensor
import Mathlib.Algebra.Module.Opposite

/-!
# Tensors over the unitization and the additive scalar comparison

Renard (9 July 2026), I.2.1 on printed p. 14 / PDF20. For a `k`-algebra `A` acting compatibly on
the right of `X` and on the left of `Y`, the unitized actions of `Unitization k A` give the
actual balanced tensor over the unitization. The comparison map from the original tensor over
`A` kills the integer span of the scalar-balancing differences and descends to the additive
quotient by that span. No coefficient module on either tensor is constructed or assumed.
-/

set_option autoImplicit false

namespace Langlands.Algebra

namespace CompatibleUnitizationTensor

open MulOpposite Unitization

universe uK uA uX uY uZ

section OppositeAdapters

variable (k : Type uK) (A : Type uA) [CommRing k] [NonUnitalRing A] [Module k A]

/-- Opposite-ring adapter: `(c • a) * b = c • (a * b)` in `Aᵐᵒᵖ`, from `SMulCommClass k A A`. -/
theorem opIsScalarTower [SMulCommClass k A A] : IsScalarTower k Aᵐᵒᵖ Aᵐᵒᵖ :=
  ⟨fun c a b => unop_injective (mul_smul_comm c b.unop a.unop)⟩

/-- Opposite-ring adapter: `c • (a * b) = a * (c • b)` in `Aᵐᵒᵖ`, from `IsScalarTower k A A`. -/
theorem opSMulCommClass [IsScalarTower k A A] : SMulCommClass k Aᵐᵒᵖ Aᵐᵒᵖ :=
  ⟨fun c a b => unop_injective (smul_mul_assoc c b.unop a.unop).symm⟩

/-- The opposite of the unitization is the unitization of the opposite ring:
`op u ↦ (u.fst, op u.snd)`. Only the multiplications and additions enter. -/
def opRingEquiv : (Unitization k A)ᵐᵒᵖ ≃+* Unitization k Aᵐᵒᵖ where
  toFun w := Unitization.mk (w.unop.fst, op w.unop.snd)
  invFun v := op (Unitization.mk (v.fst, v.snd.unop))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' w v := by
    ext
    · exact mul_comm v.unop.fst w.unop.fst
    · change op (v.unop.fst • w.unop.snd + w.unop.fst • v.unop.snd + v.unop.snd * w.unop.snd) =
        w.unop.fst • op v.unop.snd + v.unop.fst • op w.unop.snd + op w.unop.snd * op v.unop.snd
      rw [op_add, op_add, op_smul, op_smul, op_mul, add_comm (v.unop.fst • op w.unop.snd)]
  map_add' _ _ := rfl

@[simp] theorem opRingEquiv_fst (u : Unitization k A) : (opRingEquiv k A (op u)).fst = u.fst := rfl

@[simp] theorem opRingEquiv_snd (u : Unitization k A) :
    (opRingEquiv k A (op u)).snd = op u.snd := rfl

@[simp] theorem opRingEquiv_symm_fst (v : Unitization k Aᵐᵒᵖ) :
    ((opRingEquiv k A).symm v).unop.fst = v.fst := rfl

@[simp] theorem opRingEquiv_symm_snd (v : Unitization k Aᵐᵒᵖ) :
    ((opRingEquiv k A).symm v).unop.snd = v.snd.unop := rfl

/-- The complete coordinate formula of the equivalence. -/
theorem opRingEquiv_function :
    (opRingEquiv k A : (Unitization k A)ᵐᵒᵖ → Unitization k Aᵐᵒᵖ) =
      fun w => Unitization.mk (w.unop.fst, op w.unop.snd) := rfl

/-- The complete coordinate formula of the inverse equivalence. -/
theorem opRingEquiv_symm_function :
    ((opRingEquiv k A).symm : Unitization k Aᵐᵒᵖ → (Unitization k A)ᵐᵒᵖ) =
      fun v => op (Unitization.mk (v.fst, v.snd.unop)) := rfl

end OppositeAdapters

section Actions

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [Module k X] [rightAction : NonUnitalModule Aᵐᵒᵖ X]
  [rightTower : IsScalarTower k Aᵐᵒᵖ X] [rightComm : SMulCommClass k Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [leftAction : NonUnitalModule A Y]
  [leftTower : IsScalarTower k A Y] [leftComm : SMulCommClass k A Y]

/-- The original left action as the published actual homomorphism into `k`-linear maps. -/
abbrev leftEndHom : A →ₙₐ[k] Module.End k Y := NonUnitalModule.toLinearEndHom k (B := A) (V := Y)

/-- The original right action, as a left action of `Aᵐᵒᵖ`, as the published actual homomorphism
into `k`-linear maps. -/
abbrev rightEndHom : Aᵐᵒᵖ →ₙₐ[k] Module.End k X :=
  NonUnitalModule.toLinearEndHom k (B := Aᵐᵒᵖ) (V := X)

/-- The unitized left action: precisely the published `CompatibleUnitization.module`. -/
@[instance_reducible]
def leftModule : Module (Unitization k A) Y := CompatibleUnitization.module (leftEndHom k A Y)

theorem leftModule_eq :
    leftModule k A Y = CompatibleUnitization.module (NonUnitalModule.toLinearEndHom k) := rfl

/-- The unitized right action: the published unitized action of `Aᵐᵒᵖ`, transported along
`opRingEquiv`. -/
@[instance_reducible]
def rightModule : Module (Unitization k A)ᵐᵒᵖ X :=
  haveI := opIsScalarTower k A
  haveI := opSMulCommClass k A
  letI := CompatibleUnitization.module (rightEndHom k A X)
  Module.compHom X (opRingEquiv k A).toRingHom

/-- The left action as the named ambient adapter `NonUnitalModule.ofModule`. -/
@[instance_reducible]
def leftNonUnitalModule : NonUnitalModule (Unitization k A) Y :=
  @NonUnitalModule.ofModule (Unitization k A) Y _ _ (leftModule k A Y)

/-- The right action as the named ambient adapter `NonUnitalModule.ofModule`. -/
@[instance_reducible]
def rightNonUnitalModule : NonUnitalModule (Unitization k A)ᵐᵒᵖ X :=
  @NonUnitalModule.ofModule (Unitization k A)ᵐᵒᵖ X _ _ (rightModule k A X)

/-! Left action: formula, restrictions, unit law and coefficient compatibility. -/

theorem left_smul_eq (u : Unitization k A) (y : Y) :
    (letI := leftModule k A Y; u • y) = u.fst • y + u.snd • y := rfl

theorem left_smul_function :
    (fun (u : Unitization k A) (y : Y) => (letI := leftModule k A Y; u • y)) =
      fun u y => u.fst • y + u.snd • y := rfl

@[simp] theorem left_inr_smul (a : A) (y : Y) :
    (letI := leftModule k A Y; (a : Unitization k A) • y) = a • y :=
  CompatibleUnitization.inr_smul (leftEndHom k A Y) a y

@[simp] theorem left_inl_smul (c : k) (y : Y) :
    (letI := leftModule k A Y; (inl c : Unitization k A) • y) = c • y :=
  CompatibleUnitization.inl_smul (leftEndHom k A Y) c y

theorem left_one_smul (y : Y) : (letI := leftModule k A Y; (1 : Unitization k A) • y) = y :=
  CompatibleUnitization.one_smul (leftEndHom k A Y) y

theorem left_isScalarTower :
    letI := leftModule k A Y
    IsScalarTower k (Unitization k A) Y :=
  CompatibleUnitization.isScalarTower (leftEndHom k A Y)

theorem left_smulCommClass :
    letI := leftModule k A Y
    SMulCommClass k (Unitization k A) Y :=
  CompatibleUnitization.smulCommClass (leftEndHom k A Y)

/-- The ambient adapter has the same action. -/
theorem leftNonUnitalModule_smul (u : Unitization k A) (y : Y) :
    (letI := leftNonUnitalModule k A Y; u • y) = (letI := leftModule k A Y; u • y) := rfl

/-! Right action: formula, restrictions, unit law and coefficient compatibility. -/

theorem right_smul_eq (u : Unitization k A) (x : X) :
    (letI := rightModule k A X; op u • x) = u.fst • x + op u.snd • x := rfl

theorem right_smul_function :
    (fun (w : (Unitization k A)ᵐᵒᵖ) (x : X) => (letI := rightModule k A X; w • x)) =
      fun w x => w.unop.fst • x + op w.unop.snd • x := rfl

@[simp] theorem right_inr_smul (a : A) (x : X) :
    (letI := rightModule k A X; op (a : Unitization k A) • x) = op a • x := by
  rw [right_smul_eq, fst_inr, snd_inr, zero_smul, zero_add]

@[simp] theorem right_inl_smul (c : k) (x : X) :
    (letI := rightModule k A X; op (inl c : Unitization k A) • x) = c • x := by
  rw [right_smul_eq, fst_inl, snd_inl, op_zero, NonUnitalModule.zero_smul, add_zero]

theorem right_one_smul (x : X) :
    (letI := rightModule k A X; (1 : (Unitization k A)ᵐᵒᵖ) • x) = x := by
  rw [← op_one, right_smul_eq, fst_one, snd_one, op_zero, NonUnitalModule.zero_smul, add_zero,
    _root_.one_smul]

theorem right_isScalarTower :
    letI := rightModule k A X
    IsScalarTower k (Unitization k A)ᵐᵒᵖ X :=
  letI := rightModule k A X
  ⟨fun c w x => by
    change (op (c • w.unop) • x) = c • (op w.unop • x)
    rw [right_smul_eq, right_smul_eq, fst_smul, snd_smul, op_smul, smul_add,
      smul_assoc c w.unop.fst x, smul_assoc c (op w.unop.snd) x]⟩

theorem right_smulCommClass :
    letI := rightModule k A X
    SMulCommClass k (Unitization k A)ᵐᵒᵖ X :=
  letI := rightModule k A X
  ⟨fun c w x => by
    change c • (op w.unop • x) = op w.unop • (c • x)
    rw [right_smul_eq, right_smul_eq, smul_add, smul_comm c w.unop.fst x, smul_comm c (op w.unop.snd) x]⟩

/-- The ambient adapter has the same action. -/
theorem rightNonUnitalModule_smul (w : (Unitization k A)ᵐᵒᵖ) (x : X) :
    (letI := rightNonUnitalModule k A X; w • x) = (letI := rightModule k A X; w • x) := rfl

end Actions

section Tensors

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [Module k X] [rightAction : NonUnitalModule Aᵐᵒᵖ X]
  [rightTower : IsScalarTower k Aᵐᵒᵖ X] [rightComm : SMulCommClass k Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [leftAction : NonUnitalModule A Y]
  [leftTower : IsScalarTower k A Y] [leftComm : SMulCommClass k A Y]

/- Inside this section the two named adapters select the unitized actions for the published
tensor over `Unitization k A`; outside it they are passed explicitly. -/
attribute [local instance] rightNonUnitalModule leftNonUnitalModule

/-- `TU`: the published balanced tensor over `Unitization k A`, for the constructed unitized
actions passed through the named adapters `rightNonUnitalModule` and `leftNonUnitalModule`. -/
abbrev UnitizedTensor : Type (max uX uY) := NonUnitalModuleTensor.Tensor (Unitization k A) X Y

/-- The carrier with all instance arguments displayed. -/
theorem unitizedTensor_eq : UnitizedTensor k A X Y =
    @NonUnitalModuleTensor.Tensor (Unitization k A) X Y _ _ _
      (rightNonUnitalModule k A X) (leftNonUnitalModule k A Y) := rfl

/-- The inherited additive group of `TU` is the published one. -/
theorem unitizedTensor_addCommGroup_eq :
    (inferInstance : AddCommGroup (UnitizedTensor k A X Y)) =
      NonUnitalModuleTensor.addCommGroup (Unitization k A) X Y := rfl

/-- The pure map of `TU`: the published `NonUnitalModuleTensor.tmul` over the unitization. -/
def unitizedTmul (x : X) (y : Y) : UnitizedTensor k A X Y :=
  NonUnitalModuleTensor.tmul (Unitization k A) X Y x y

theorem unitizedTmul_function :
    unitizedTmul k A X Y = NonUnitalModuleTensor.tmul (Unitization k A) X Y := rfl

/-- The biadditive pure map of `TU`: the published `NonUnitalModuleTensor.biadditive`. -/
def unitizedBiadditive : X →+ Y →+ UnitizedTensor k A X Y :=
  NonUnitalModuleTensor.biadditive (Unitization k A) X Y

@[simp] theorem unitizedBiadditive_apply (x : X) (y : Y) :
    unitizedBiadditive k A X Y x y = unitizedTmul k A X Y x y := rfl

theorem unitizedBiadditive_function :
    (fun x y => unitizedBiadditive k A X Y x y) = unitizedTmul k A X Y := rfl

/-- Actual balancing of `TU` over the unitization, for the constructed actions. -/
theorem unitizedTmul_balanced (u : Unitization k A) (x : X) (y : Y) :
    unitizedTmul k A X Y (letI := rightModule k A X; op u • x) y =
      unitizedTmul k A X Y x (letI := leftModule k A Y; u • y) :=
  NonUnitalModuleTensor.tmul_balanced (Unitization k A) X Y u x y

/-- The `TU` pure map is balanced for the original actions of `A`. -/
theorem unitizedTmul_original (a : A) (x : X) (y : Y) :
    unitizedTmul k A X Y (op a • x) y = unitizedTmul k A X Y x (a • y) := by
  have h := unitizedTmul_balanced k A X Y (a : Unitization k A) x y
  rwa [right_inr_smul, left_inr_smul] at h

/-- The `TU` pure map is balanced for the displayed `k`-scalars. -/
theorem unitizedTmul_scalar (c : k) (x : X) (y : Y) :
    unitizedTmul k A X Y (c • x) y = unitizedTmul k A X Y x (c • y) := by
  have h := unitizedTmul_balanced k A X Y (inl c) x y
  rwa [right_inl_smul, left_inl_smul] at h

variable {X Y}
variable {Z : Type uZ} [AddCommGroup Z]

/-- Balancing of a biadditive map for the given `k`-scalars on the two factors. -/
def IsScalarBalanced (b : X →+ Y →+ Z) : Prop :=
  ∀ (c : k) (x : X) (y : Y), b (c • x) y = b x (c • y)

/-- Balancing over the unitization is original `A`-balancing together with `k`-balancing. -/
theorem isBalanced_unitization_iff (b : X →+ Y →+ Z) :
    NonUnitalModuleTensor.IsBalanced (Unitization k A) b ↔
      NonUnitalModuleTensor.IsBalanced A b ∧ IsScalarBalanced k b := by
  constructor
  · intro h
    refine ⟨fun a x y => ?_, fun c x y => ?_⟩
    · have h' := h (a : Unitization k A) x y
      change b (letI := rightModule k A X; op (a : Unitization k A) • x) y =
        b x (letI := leftModule k A Y; (a : Unitization k A) • y) at h'
      rwa [right_inr_smul, left_inr_smul] at h'
    · have h' := h (inl c) x y
      change b (letI := rightModule k A X; op (inl c : Unitization k A) • x) y =
        b x (letI := leftModule k A Y; (inl c : Unitization k A) • y) at h'
      rwa [right_inl_smul, left_inl_smul] at h'
  · rintro ⟨ha, hc⟩ u x y
    rw [right_smul_eq, left_smul_eq, map_add, AddMonoidHom.add_apply, map_add, hc, ha]

/-- The universal additive lift from `TU`: the published `NonUnitalModuleTensor.lift` over the
unitization, for a biadditive map balanced for the original actions and for the scalars. -/
def unitizedLift (b : X →+ Y →+ Z) (ha : NonUnitalModuleTensor.IsBalanced A b)
    (hc : IsScalarBalanced k b) : UnitizedTensor k A X Y →+ Z :=
  NonUnitalModuleTensor.lift (Unitization k A) b ((isBalanced_unitization_iff k A b).mpr ⟨ha, hc⟩)

/-- The complete underlying map of the lift. -/
theorem unitizedLift_eq (b : X →+ Y →+ Z) (ha : NonUnitalModuleTensor.IsBalanced A b)
    (hc : IsScalarBalanced k b) :
    unitizedLift k A b ha hc =
      NonUnitalModuleTensor.lift (Unitization k A) b
        ((isBalanced_unitization_iff k A b).mpr ⟨ha, hc⟩) := rfl

/-- The lift composed with the projection is the canonical integer lift. -/
theorem unitizedLift_comp_projection (b : X →+ Y →+ Z)
    (ha : NonUnitalModuleTensor.IsBalanced A b) (hc : IsScalarBalanced k b) :
    (unitizedLift k A b ha hc).comp (NonUnitalModuleTensor.projection (Unitization k A) X Y) =
      NonUnitalModuleTensor.integerLift b := rfl

@[simp] theorem unitizedLift_tmul (b : X →+ Y →+ Z) (ha : NonUnitalModuleTensor.IsBalanced A b)
    (hc : IsScalarBalanced k b) (x : X) (y : Y) :
    unitizedLift k A b ha hc (unitizedTmul k A X Y x y) = b x y := rfl

theorem unitizedLift_pure_function (b : X →+ Y →+ Z)
    (ha : NonUnitalModuleTensor.IsBalanced A b) (hc : IsScalarBalanced k b) :
    (fun x y => unitizedLift k A b ha hc (unitizedTmul k A X Y x y)) = fun x y => b x y := rfl

/-- Additive maps out of `TU` are determined by their pure-tensor values. -/
theorem unitizedHom_ext {f g : UnitizedTensor k A X Y →+ Z}
    (h : ∀ (x : X) (y : Y), f (unitizedTmul k A X Y x y) = g (unitizedTmul k A X Y x y)) :
    f = g :=
  NonUnitalModuleTensor.hom_ext (Unitization k A) h

/-- Uniqueness of the lift, as equality of complete additive maps. -/
theorem unitizedLift_unique (b : X →+ Y →+ Z) (ha : NonUnitalModuleTensor.IsBalanced A b)
    (hc : IsScalarBalanced k b) (f : UnitizedTensor k A X Y →+ Z)
    (hf : ∀ x y, f (unitizedTmul k A X Y x y) = b x y) : f = unitizedLift k A b ha hc :=
  NonUnitalModuleTensor.lift_unique (Unitization k A) b _ f hf

end Tensors

section Comparison

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [Module k X] [rightAction : NonUnitalModule Aᵐᵒᵖ X]
  [rightTower : IsScalarTower k Aᵐᵒᵖ X] [rightComm : SMulCommClass k Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [leftAction : NonUnitalModule A Y]
  [leftTower : IsScalarTower k A Y] [leftComm : SMulCommClass k A Y]

attribute [local instance] rightNonUnitalModule leftNonUnitalModule

/-- The `TU` pure map is balanced for the original actions. -/
theorem unitizedBiadditive_isBalanced :
    NonUnitalModuleTensor.IsBalanced A (unitizedBiadditive k A X Y) :=
  unitizedTmul_original k A X Y

/-- `q : TA →+ TU`: precisely the published lift from the original tensor of the `TU` pure map. -/
def comparison : NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor k A X Y :=
  NonUnitalModuleTensor.lift A (unitizedBiadditive k A X Y) (unitizedBiadditive_isBalanced k A X Y)

/-- The complete underlying lift of `q`. -/
theorem comparison_eq : comparison k A X Y =
    NonUnitalModuleTensor.lift A (unitizedBiadditive k A X Y)
      (unitizedBiadditive_isBalanced k A X Y) := rfl

@[simp] theorem comparison_tmul (x : X) (y : Y) :
    comparison k A X Y (NonUnitalModuleTensor.tmul A X Y x y) = unitizedTmul k A X Y x y := rfl

theorem comparison_pure_function :
    (fun x y => comparison k A X Y (NonUnitalModuleTensor.tmul A X Y x y)) =
      unitizedTmul k A X Y := rfl

/-- Factorization through the published integer-tensor projection of `TA`. -/
theorem comparison_comp_projection :
    (comparison k A X Y).comp (NonUnitalModuleTensor.projection A X Y) =
      NonUnitalModuleTensor.integerLift (unitizedBiadditive k A X Y) := rfl

/-- On the integer tensor, `q` turns the projection of `TA` into the projection of `TU`. -/
theorem comparison_comp_projection_eq :
    (comparison k A X Y).comp (NonUnitalModuleTensor.projection A X Y) =
      NonUnitalModuleTensor.projection (Unitization k A) X Y := by
  apply AddMonoidHom.toIntLinearMap_injective
  exact TensorProduct.ext' fun _ _ => rfl

/-- `q` is surjective: `TU` is generated by pure tensors, all of which are values of `q`. -/
theorem comparison_surjective : Function.Surjective (comparison k A X Y) := by
  intro t
  obtain ⟨p, rfl⟩ := NonUnitalModuleTensor.projection_surjective (Unitization k A) X Y t
  induction p using TensorProduct.inductionOn with
  | tmul x y => exact ⟨NonUnitalModuleTensor.tmul A X Y x y, rfl⟩
  | add p p' hp hp' =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨s', hs'⟩ := hp'
    exact ⟨s + s', by rw [map_add, hs, hs', map_add]⟩

/-- `H`: the canonical integer span, in the original tensor, of the scalar-balancing
differences. The integer action on `TA` is the one of its inherited additive group. -/
def scalarRelations : Submodule ℤ (NonUnitalModuleTensor.Tensor A X Y) :=
  Submodule.span ℤ (Set.range fun p : k × X × Y =>
    NonUnitalModuleTensor.tmul A X Y (p.1 • p.2.1) p.2.2 -
      NonUnitalModuleTensor.tmul A X Y p.2.1 (p.1 • p.2.2))

omit [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] rightTower rightComm leftTower
  leftComm in
theorem scalarDifference_mem (c : k) (x : X) (y : Y) :
    NonUnitalModuleTensor.tmul A X Y (c • x) y - NonUnitalModuleTensor.tmul A X Y x (c • y) ∈
      scalarRelations k A X Y :=
  Submodule.subset_span ⟨(c, x, y), rfl⟩

/-- `Q = TA ⧸ H`, with its inherited additive group. -/
abbrev ScalarQuotient : Type (max uX uY) :=
  NonUnitalModuleTensor.Tensor A X Y ⧸ scalarRelations k A X Y

/-- `q` kills the scalar relations. -/
theorem scalarRelations_le_ker :
    scalarRelations k A X Y ≤ LinearMap.ker (comparison k A X Y).toIntLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨c, x, y⟩, rfl⟩
  change comparison k A X Y (NonUnitalModuleTensor.tmul A X Y (c • x) y -
    NonUnitalModuleTensor.tmul A X Y x (c • y)) = 0
  rw [map_sub, comparison_tmul, comparison_tmul, unitizedTmul_scalar, sub_self]

/-- `qbar : Q →+ TU`, the descent of `q` through the quotient by `H`. -/
def descendedComparison : ScalarQuotient k A X Y →+ UnitizedTensor k A X Y :=
  ((scalarRelations k A X Y).liftQ (comparison k A X Y).toIntLinearMap
    (scalarRelations_le_ker k A X Y)).toAddMonoidHom

/-- The complete underlying quotient lift of `qbar`. -/
theorem descendedComparison_eq : descendedComparison k A X Y =
    ((scalarRelations k A X Y).liftQ (comparison k A X Y).toIntLinearMap
      (scalarRelations_le_ker k A X Y)).toAddMonoidHom := rfl

@[simp] theorem descendedComparison_mk (t : NonUnitalModuleTensor.Tensor A X Y) :
    descendedComparison k A X Y (Submodule.Quotient.mk t) = comparison k A X Y t := rfl

@[simp] theorem descendedComparison_mk_tmul (x : X) (y : Y) :
    descendedComparison k A X Y (Submodule.Quotient.mk (NonUnitalModuleTensor.tmul A X Y x y)) =
      unitizedTmul k A X Y x y := rfl

/-- `qbar ∘ H.mkQ = q`, as equality of complete additive maps. -/
theorem descendedComparison_comp_mkQ :
    (descendedComparison k A X Y).comp (scalarRelations k A X Y).mkQ.toAddMonoidHom =
      comparison k A X Y := rfl

end Comparison

/-! ## Examples and diagnostics -/

noncomputable section Examples

/-! ### The complex specialization at independent universes

The source setting `k = ℂ`, with the algebra, the two factors and the target in independent
universes and no dimension hypothesis. -/

section ComplexSpecialization

example : ∀ (A : Type uA) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    Module (Unitization ℂ A) Y :=
  fun A Y => @leftModule ℂ A Y _

example : ∀ (A : Type uA) (X : Type uX)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X],
    Module (Unitization ℂ A)ᵐᵒᵖ X :=
  fun A X => @rightModule ℂ A X _

example : ∀ (A : Type uA) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    NonUnitalModule (Unitization ℂ A) Y :=
  fun A Y => @leftNonUnitalModule ℂ A Y _

example : ∀ (A : Type uA) (X : Type uX)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X],
    NonUnitalModule (Unitization ℂ A)ᵐᵒᵖ X :=
  fun A X => @rightNonUnitalModule ℂ A X _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    Type (max uX uY) :=
  fun A X Y => @UnitizedTensor ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    ∀ (c : ℂ) (x : X) (y : Y),
      unitizedTmul ℂ A X Y (c • x) y = unitizedTmul ℂ A X Y x (c • y) :=
  fun A X Y => @unitizedTmul_scalar ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    ∀ (a : A) (x : X) (y : Y),
      unitizedTmul ℂ A X Y (MulOpposite.op a • x) y = unitizedTmul ℂ A X Y x (a • y) :=
  fun A X Y => @unitizedTmul_original ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor ℂ A X Y :=
  fun A X Y => @comparison ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    Function.Surjective (comparison ℂ A X Y) :=
  fun A X Y => @comparison_surjective ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y],
    Submodule ℤ (NonUnitalModuleTensor.Tensor A X Y) :=
  fun A X Y => @scalarRelations ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y],
    Type (max uX uY) :=
  fun A X Y => @ScalarQuotient ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    scalarRelations ℂ A X Y ≤ LinearMap.ker (comparison ℂ A X Y).toIntLinearMap :=
  fun A X Y => @scalarRelations_le_ker ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    ScalarQuotient ℂ A X Y →+ UnitizedTensor ℂ A X Y :=
  fun A X Y => @descendedComparison ℂ A X Y _

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y]
    {Z : Type uZ} [AddCommGroup Z] (b : X →+ Y →+ Z),
    @NonUnitalModuleTensor.IsBalanced (Unitization ℂ A) X Y _ _ _
        (rightNonUnitalModule ℂ A X) (leftNonUnitalModule ℂ A Y) Z _ b ↔
        NonUnitalModuleTensor.IsBalanced A b ∧ IsScalarBalanced ℂ b :=
  fun A {X} {Y} => @isBalanced_unitization_iff ℂ A X Y _

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y]
    {Z : Type uZ} [AddCommGroup Z] (b : X →+ Y →+ Z),
    NonUnitalModuleTensor.IsBalanced A b → IsScalarBalanced ℂ b →
      UnitizedTensor ℂ A X Y →+ Z :=
  fun A {X} {Y} => @unitizedLift ℂ A X Y _

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [AddCommGroup X] [Module ℂ X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower ℂ Aᵐᵒᵖ X] [SMulCommClass ℂ Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module ℂ Y] [NonUnitalModule A Y]
    [IsScalarTower ℂ A Y] [SMulCommClass ℂ A Y],
    (descendedComparison ℂ A X Y).comp
      (scalarRelations ℂ A X Y).mkQ.toAddMonoidHom = comparison ℂ A X Y :=
  fun A X Y => @descendedComparison_comp_mkQ ℂ A X Y _

end ComplexSpecialization

/-! ### Complete unapplied interfaces at independent universes -/

section ArbitraryUniverses

example : ∀ (k : Type uK) (A : Type uA) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    Module (Unitization k A) Y :=
  @leftModule

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X],
    Module (Unitization k A)ᵐᵒᵖ X :=
  @rightModule

example : ∀ (k : Type uK) (A : Type uA) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    NonUnitalModule (Unitization k A) Y :=
  @leftNonUnitalModule

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X],
    NonUnitalModule (Unitization k A)ᵐᵒᵖ X :=
  @rightNonUnitalModule

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    Type (max uX uY) :=
  @UnitizedTensor

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor k A X Y :=
  @comparison

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y],
    Submodule ℤ (NonUnitalModuleTensor.Tensor A X Y) :=
  @scalarRelations

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y],
    Type (max uX uY) :=
  @ScalarQuotient

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    ScalarQuotient k A X Y →+ UnitizedTensor k A X Y :=
  @descendedComparison

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y]
    {Z : Type uZ} [AddCommGroup Z] (b : X →+ Y →+ Z),
    @NonUnitalModuleTensor.IsBalanced (Unitization k A) X Y _ _ _
        (rightNonUnitalModule k A X) (leftNonUnitalModule k A Y) Z _ b ↔
        NonUnitalModuleTensor.IsBalanced A b ∧ IsScalarBalanced k b :=
  @isBalanced_unitization_iff

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y]
    {Z : Type uZ} [AddCommGroup Z] (b : X →+ Y →+ Z),
    NonUnitalModuleTensor.IsBalanced A b → IsScalarBalanced k b →
      UnitizedTensor k A X Y →+ Z :=
  @unitizedLift

end ArbitraryUniverses

/-! Unequal universes `(uK, uA, uX, uY, uZ) = (0, 1, 0, 1, 0)`. -/

section ZeroOneZeroOne

example : ∀ (k : Type 0) (A : Type 1) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    Module (Unitization k A) Y :=
  @leftModule

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X],
    Module (Unitization k A)ᵐᵒᵖ X :=
  @rightModule

example : ∀ (k : Type 0) (A : Type 1) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    NonUnitalModule (Unitization k A) Y :=
  @leftNonUnitalModule

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X],
    NonUnitalModule (Unitization k A)ᵐᵒᵖ X :=
  @rightNonUnitalModule

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    Type (max 0 1) :=
  @UnitizedTensor

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor k A X Y :=
  @comparison

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y],
    Submodule ℤ (NonUnitalModuleTensor.Tensor A X Y) :=
  @scalarRelations

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y],
    Type (max 0 1) :=
  @ScalarQuotient

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    ScalarQuotient k A X Y →+ UnitizedTensor k A X Y :=
  @descendedComparison

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y]
    {Z : Type 0} [AddCommGroup Z] (b : X →+ Y →+ Z),
    @NonUnitalModuleTensor.IsBalanced (Unitization k A) X Y _ _ _
        (rightNonUnitalModule k A X) (leftNonUnitalModule k A Y) Z _ b ↔
        NonUnitalModuleTensor.IsBalanced A b ∧ IsScalarBalanced k b :=
  @isBalanced_unitization_iff

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y]
    {Z : Type 0} [AddCommGroup Z] (b : X →+ Y →+ Z),
    NonUnitalModuleTensor.IsBalanced A b → IsScalarBalanced k b →
      UnitizedTensor k A X Y →+ Z :=
  @unitizedLift

end ZeroOneZeroOne

/-! Unequal universes `(uK, uA, uX, uY, uZ) = (1, 0, 1, 0, 1)`. -/

section OneZeroOneZero

example : ∀ (k : Type 1) (A : Type 0) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    Module (Unitization k A) Y :=
  @leftModule

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X],
    Module (Unitization k A)ᵐᵒᵖ X :=
  @rightModule

example : ∀ (k : Type 1) (A : Type 0) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    NonUnitalModule (Unitization k A) Y :=
  @leftNonUnitalModule

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X],
    NonUnitalModule (Unitization k A)ᵐᵒᵖ X :=
  @rightNonUnitalModule

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    Type (max 1 0) :=
  @UnitizedTensor

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor k A X Y :=
  @comparison

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y],
    Submodule ℤ (NonUnitalModuleTensor.Tensor A X Y) :=
  @scalarRelations

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y],
    Type (max 1 0) :=
  @ScalarQuotient

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    ScalarQuotient k A X Y →+ UnitizedTensor k A X Y :=
  @descendedComparison

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y]
    {Z : Type 1} [AddCommGroup Z] (b : X →+ Y →+ Z),
    @NonUnitalModuleTensor.IsBalanced (Unitization k A) X Y _ _ _
        (rightNonUnitalModule k A X) (leftNonUnitalModule k A Y) Z _ b ↔
        NonUnitalModuleTensor.IsBalanced A b ∧ IsScalarBalanced k b :=
  @isBalanced_unitization_iff

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y]
    {Z : Type 1} [AddCommGroup Z] (b : X →+ Y →+ Z),
    NonUnitalModuleTensor.IsBalanced A b → IsScalarBalanced k b →
      UnitizedTensor k A X Y →+ Z :=
  @unitizedLift

end OneZeroOneZero

/-! ### Explicit original choices under competing structures -/

section CompetingCoefficientsAndActions

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y]
  [originalXScalars : Module k X] [originalYScalars : Module k Y]
  [originalRight : NonUnitalModule Aᵐᵒᵖ X] [originalLeft : NonUnitalModule A Y]
  [originalRightTower : IsScalarTower k Aᵐᵒᵖ X] [originalRightComm : SMulCommClass k Aᵐᵒᵖ X]
  [originalLeftTower : IsScalarTower k A Y] [originalLeftComm : SMulCommClass k A Y]
  [competingXScalars : Module k X] [competingYScalars : Module k Y]
  [competingRight : NonUnitalModule Aᵐᵒᵖ X] [competingLeft : NonUnitalModule A Y]

/-- The unitized left action uses the selected scalars and the selected original action. -/
example (u : Unitization k A) (y : Y) :
    (@leftModule k A Y _ _ _ _ _ _ originalYScalars originalLeft originalLeftTower
        originalLeftComm).smul u y =
      originalYScalars.smul u.fst y + originalLeft.smul u.snd y := rfl

/-- The unitized right action uses the selected scalars and the selected original action. -/
example (u : Unitization k A) (x : X) :
    (@rightModule k A X _ _ _ _ _ _ originalXScalars originalRight originalRightTower
        originalRightComm).smul (op u) x =
      originalXScalars.smul u.fst x + originalRight.smul (op u.snd) x := rfl

/-- Restricting the left adapter along `inr` recovers the selected original action. -/
example (a : A) (y : Y) :
    (@leftNonUnitalModule k A Y _ _ _ _ _ _ originalYScalars originalLeft originalLeftTower
        originalLeftComm).smul (a : Unitization k A) y = originalLeft.smul a y :=
  @left_inr_smul k A Y _ _ _ _ _ _ originalYScalars originalLeft originalLeftTower
    originalLeftComm a y

/-- Restricting the right adapter along `inr` recovers the selected original action. -/
example (a : A) (x : X) :
    (@rightNonUnitalModule k A X _ _ _ _ _ _ originalXScalars originalRight originalRightTower
        originalRightComm).smul (op (a : Unitization k A)) x = originalRight.smul (op a) x :=
  @right_inr_smul k A X _ _ _ _ _ _ originalXScalars originalRight originalRightTower
    originalRightComm a x

/-- The carrier `TU` is the published tensor for the selected unitized adapters. -/
example :
    @UnitizedTensor k A X Y _ _ _ _ _ _ originalXScalars originalRight originalRightTower
        originalRightComm _ originalYScalars originalLeft originalLeftTower originalLeftComm =
      @NonUnitalModuleTensor.Tensor (Unitization k A) X Y _ _ _
        (@rightNonUnitalModule k A X _ _ _ _ _ _ originalXScalars originalRight
          originalRightTower originalRightComm)
        (@leftNonUnitalModule k A Y _ _ _ _ _ _ originalYScalars originalLeft
          originalLeftTower originalLeftComm) := rfl

/-- The generators of `H` use the selected scalars and the selected original tensor. -/
example :
    @scalarRelations k A X Y _ _ _ originalXScalars originalRight _ originalYScalars
        originalLeft =
      Submodule.span ℤ (Set.range fun p : k × X × Y =>
        @NonUnitalModuleTensor.tmul A X Y _ _ _ originalRight originalLeft
            (originalXScalars.smul p.1 p.2.1) p.2.2 -
          @NonUnitalModuleTensor.tmul A X Y _ _ _ originalRight originalLeft p.2.1
            (originalYScalars.smul p.1 p.2.2)) := rfl

/-- `q` sends selected original pure tensors to selected unitized pure tensors. -/
example (x : X) (y : Y) :
    @comparison k A X Y _ _ _ _ _ _ originalXScalars originalRight originalRightTower
        originalRightComm _ originalYScalars originalLeft originalLeftTower originalLeftComm
        (@NonUnitalModuleTensor.tmul A X Y _ _ _ originalRight originalLeft x y) =
      @unitizedTmul k A X Y _ _ _ _ _ _ originalXScalars originalRight originalRightTower
        originalRightComm _ originalYScalars originalLeft originalLeftTower originalLeftComm
        x y := rfl

/-- `qbar` for the selected structures, as a complete additive map. -/
example :
    @ScalarQuotient k A X Y _ _ _ originalXScalars originalRight _ originalYScalars
        originalLeft →+
      @UnitizedTensor k A X Y _ _ _ _ _ _ originalXScalars originalRight originalRightTower
        originalRightComm _ originalYScalars originalLeft originalLeftTower originalLeftComm :=
  @descendedComparison k A X Y _ _ _ _ _ _ originalXScalars originalRight originalRightTower
    originalRightComm _ originalYScalars originalLeft originalLeftTower originalLeftComm

end CompetingCoefficientsAndActions

section CompetingGroups

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [originalXGroup : AddCommGroup X] [originalYGroup : AddCommGroup Y]
  [Module k X] [NonUnitalModule Aᵐᵒᵖ X] [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
  [Module k Y] [NonUnitalModule A Y] [IsScalarTower k A Y] [SMulCommClass k A Y]
  [competingXGroup : AddCommGroup X] [competingYGroup : AddCommGroup Y]

/-- `q` for the selected additive groups of the factors. -/
example :
    letI := originalXGroup
    letI := originalYGroup
    NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor k A X Y :=
  @comparison k A X Y _ _ _ _ _ originalXGroup _ _ _ _ originalYGroup _ _ _ _

/-- `qbar` for the selected additive groups of the factors. -/
example :
    letI := originalXGroup
    letI := originalYGroup
    ScalarQuotient k A X Y →+ UnitizedTensor k A X Y :=
  @descendedComparison k A X Y _ _ _ _ _ originalXGroup _ _ _ _ originalYGroup _ _ _ _

/-- The universal lift for the selected additive groups of the factors. -/
example :
    letI := originalXGroup
    letI := originalYGroup
    ∀ {Z : Type uZ} [AddCommGroup Z] (b : X →+ Y →+ Z),
      NonUnitalModuleTensor.IsBalanced A b → IsScalarBalanced k b →
        UnitizedTensor k A X Y →+ Z :=
  @unitizedLift k A X Y _ _ _ _ _ originalXGroup _ _ _ _ originalYGroup _ _ _ _

end CompetingGroups

section CompetingRings

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [originalRing : CommRing k] [originalAlgebra : NonUnitalRing A]
  [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
  [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
  [IsScalarTower k A Y] [SMulCommClass k A Y]
  [competingRing : CommRing k] [competingAlgebra : NonUnitalRing A]

/-- `q` for the selected coefficient ring and the selected algebra. -/
example :
    letI := originalRing
    letI := originalAlgebra
    NonUnitalModuleTensor.Tensor A X Y →+ UnitizedTensor k A X Y :=
  @comparison k A X Y originalRing originalAlgebra _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `qbar` for the selected coefficient ring and the selected algebra. -/
example :
    letI := originalRing
    letI := originalAlgebra
    ScalarQuotient k A X Y →+ UnitizedTensor k A X Y :=
  @descendedComparison k A X Y originalRing originalAlgebra _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The balancing interface for the selected coefficient ring and the selected algebra. -/
example :
    letI := originalRing
    letI := originalAlgebra
    ∀ {Z : Type uZ} [AddCommGroup Z] (b : X →+ Y →+ Z),
      @NonUnitalModuleTensor.IsBalanced (Unitization k A) X Y _ _ _
          (rightNonUnitalModule k A X) (leftNonUnitalModule k A Y) Z _ b ↔
        NonUnitalModuleTensor.IsBalanced A b ∧ IsScalarBalanced k b :=
  @isBalanced_unitization_iff k A X Y originalRing originalAlgebra _ _ _ _ _ _ _ _ _ _ _ _ _

end CompetingRings

section CompetingIntegerScalars

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]

/-- The integer scalars on `TA` are those of its inherited additive group. -/
example :
    (inferInstance : Module ℤ (NonUnitalModuleTensor.Tensor A X Y)) =
      AddCommGroup.toIntModule (NonUnitalModuleTensor.Tensor A X Y) := rfl

/-- `H` is a submodule for the canonical integer scalars of the published additive group of
`TA`, even when a competing integer module is in scope. -/
example [_competingIntegers : Module ℤ (NonUnitalModuleTensor.Tensor A X Y)] :
    @Submodule ℤ (NonUnitalModuleTensor.Tensor A X Y) _ _
      (AddCommGroup.toIntModule (NonUnitalModuleTensor.Tensor A X Y)) :=
  scalarRelations k A X Y

end CompetingIntegerScalars

section SubsingletonFactors

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
  [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
  [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
  [IsScalarTower k A Y] [SMulCommClass k A Y]

/-- A subsingleton right factor: `TA`, `TU` and `Q` are subsingletons, `H` is everything and
`qbar` is bijective. -/
example [Subsingleton X] :
    Subsingleton (NonUnitalModuleTensor.Tensor A X Y) ∧ Subsingleton (UnitizedTensor k A X Y) ∧
      Subsingleton (ScalarQuotient k A X Y) ∧ scalarRelations k A X Y = ⊤ ∧
      Function.Bijective (descendedComparison k A X Y) := by
  have hz (t : NonUnitalModuleTensor.Tensor A X Y) : t = 0 := by
    obtain ⟨p, rfl⟩ := NonUnitalModuleTensor.projection_surjective A X Y t
    induction p using TensorProduct.inductionOn with
    | tmul x y =>
      change NonUnitalModuleTensor.tmul A X Y x y = 0
      rw [Subsingleton.elim x 0, NonUnitalModuleTensor.zero_tmul]
    | add p p' hp hp' => rw [map_add, hp, hp', add_zero]
  have hA : Subsingleton (NonUnitalModuleTensor.Tensor A X Y) :=
    ⟨fun s t => (hz s).trans (hz t).symm⟩
  have hQ : Subsingleton (ScalarQuotient k A X Y) := (Submodule.mkQ_surjective _).subsingleton
  refine ⟨hA, (comparison_surjective k A X Y).subsingleton, hQ,
    eq_top_iff.mpr fun t _ => (hz t) ▸ zero_mem _, fun _ _ _ => Subsingleton.elim _ _,
    fun t => ?_⟩
  obtain ⟨s, rfl⟩ := comparison_surjective k A X Y t
  exact ⟨Submodule.Quotient.mk s, rfl⟩

/-- A subsingleton left factor: `TA`, `TU` and `Q` are subsingletons, `H` is everything and
`qbar` is bijective. -/
example [Subsingleton Y] :
    Subsingleton (NonUnitalModuleTensor.Tensor A X Y) ∧ Subsingleton (UnitizedTensor k A X Y) ∧
      Subsingleton (ScalarQuotient k A X Y) ∧ scalarRelations k A X Y = ⊤ ∧
      Function.Bijective (descendedComparison k A X Y) := by
  have hz (t : NonUnitalModuleTensor.Tensor A X Y) : t = 0 := by
    obtain ⟨p, rfl⟩ := NonUnitalModuleTensor.projection_surjective A X Y t
    induction p using TensorProduct.inductionOn with
    | tmul x y =>
      change NonUnitalModuleTensor.tmul A X Y x y = 0
      rw [Subsingleton.elim y 0, NonUnitalModuleTensor.tmul_zero]
    | add p p' hp hp' => rw [map_add, hp, hp', add_zero]
  have hA : Subsingleton (NonUnitalModuleTensor.Tensor A X Y) :=
    ⟨fun s t => (hz s).trans (hz t).symm⟩
  have hQ : Subsingleton (ScalarQuotient k A X Y) := (Submodule.mkQ_surjective _).subsingleton
  refine ⟨hA, (comparison_surjective k A X Y).subsingleton, hQ,
    eq_top_iff.mpr fun t _ => (hz t) ▸ zero_mem _, fun _ _ _ => Subsingleton.elim _ _,
    fun t => ?_⟩
  obtain ⟨s, rfl⟩ := comparison_surjective k A X Y t
  exact ⟨Submodule.Quotient.mk s, rfl⟩

end SubsingletonFactors

/-! ### Zero original actions of `ℂ` on `ℂ`

Here `k = A = X = Y = ℂ` and both original actions are `NonUnitalModule.zero`, passed by name
together with `NonUnitalModule.isScalarTower_zero` and `NonUnitalModule.smulCommClass_zero`. A
local zero instance `NonUnitalModule ℂ ℂ` would capture the notation `c • y` (the ambient action
has priority 1200), so no such instance is installed in the statements. -/

section ComplexZeroActions

local notation "zeroTmulA" =>
  @NonUnitalModuleTensor.tmul ℂ ℂ ℂ _ _ _ NonUnitalModule.zero NonUnitalModule.zero

local notation "zeroRelation" =>
  zeroTmulA (Complex.I • (1 : ℂ)) (1 : ℂ) - zeroTmulA (1 : ℂ) (Complex.I • (1 : ℂ))

local notation "zeroLeftModule" =>
  leftModule ℂ ℂ ℂ (leftAction := NonUnitalModule.zero)
    (leftTower := NonUnitalModule.isScalarTower_zero)
    (leftComm := NonUnitalModule.smulCommClass_zero)

local notation "zeroRightModule" =>
  rightModule ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
    (rightTower := NonUnitalModule.isScalarTower_zero)
    (rightComm := NonUnitalModule.smulCommClass_zero)

local notation "zeroComparison" =>
  comparison ℂ ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
    (rightTower := NonUnitalModule.isScalarTower_zero)
    (rightComm := NonUnitalModule.smulCommClass_zero) (leftAction := NonUnitalModule.zero)
    (leftTower := NonUnitalModule.isScalarTower_zero)
    (leftComm := NonUnitalModule.smulCommClass_zero)

local notation "zeroUnitizedTmul" =>
  unitizedTmul ℂ ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
    (rightTower := NonUnitalModule.isScalarTower_zero)
    (rightComm := NonUnitalModule.smulCommClass_zero) (leftAction := NonUnitalModule.zero)
    (leftTower := NonUnitalModule.isScalarTower_zero)
    (leftComm := NonUnitalModule.smulCommClass_zero)

/-- The original actions keep no unit law: `inr 1` acts by zero on both sides, while the unit of
the unitization acts by the identity. -/
example :
    (letI := zeroLeftModule; (inr (1 : ℂ) : Unitization ℂ ℂ) • (1 : ℂ)) = 0 ∧
      (letI := zeroLeftModule; (1 : Unitization ℂ ℂ) • (1 : ℂ)) = 1 ∧
      (letI := zeroRightModule; op (inr (1 : ℂ) : Unitization ℂ ℂ) • (1 : ℂ)) = 0 ∧
      (letI := zeroRightModule; (1 : (Unitization ℂ ℂ)ᵐᵒᵖ) • (1 : ℂ)) = 1 :=
  ⟨left_inr_smul ℂ ℂ ℂ (leftAction := NonUnitalModule.zero)
      (leftTower := NonUnitalModule.isScalarTower_zero)
      (leftComm := NonUnitalModule.smulCommClass_zero) 1 1,
    left_one_smul ℂ ℂ ℂ (leftAction := NonUnitalModule.zero)
      (leftTower := NonUnitalModule.isScalarTower_zero)
      (leftComm := NonUnitalModule.smulCommClass_zero) 1,
    right_inr_smul ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
      (rightTower := NonUnitalModule.isScalarTower_zero)
      (rightComm := NonUnitalModule.smulCommClass_zero) 1 1,
    right_one_smul ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
      (rightTower := NonUnitalModule.isScalarTower_zero)
      (rightComm := NonUnitalModule.smulCommClass_zero) 1⟩

/-- The scalar relation at `(I, 1, 1)` is nonzero in `TA`: the conjugate pairing
`(x, y) ↦ conj x * y` is balanced for the zero original actions and takes the value `-2 * I` on
it. The relation is a generator of `H`, it is killed by `q`, so `q` is not injective, and its
class in `Q` is zero. -/
example :
    zeroRelation ≠ 0 ∧
      zeroRelation ∈ scalarRelations ℂ ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
        (leftAction := NonUnitalModule.zero) ∧
      zeroComparison zeroRelation = 0 ∧ ¬ Function.Injective zeroComparison ∧
      (Submodule.Quotient.mk zeroRelation : ScalarQuotient ℂ ℂ ℂ ℂ
        (rightAction := NonUnitalModule.zero) (leftAction := NonUnitalModule.zero)) = 0 := by
  have hne : zeroRelation ≠ 0 := by
    let b : ℂ →+ ℂ →+ ℂ := AddMonoidHom.mul.comp (starRingEnd ℂ).toAddMonoidHom
    have hb : @NonUnitalModuleTensor.IsBalanced ℂ ℂ ℂ _ _ _ NonUnitalModule.zero
        NonUnitalModule.zero ℂ _ b := fun a x y => by
      change b 0 y = b x 0
      simp
    intro ht
    have h := congrArg (@NonUnitalModuleTensor.lift ℂ ℂ ℂ _ _ _ NonUnitalModule.zero
      NonUnitalModule.zero ℂ _ b hb) ht
    rw [map_sub, NonUnitalModuleTensor.lift_tmul, NonUnitalModuleTensor.lift_tmul,
      map_zero] at h
    change b (Complex.I * 1) 1 - b 1 (Complex.I * 1) = 0 at h
    have hv : b (Complex.I * 1) 1 - b 1 (Complex.I * 1) = -2 * Complex.I := by
      simp [b]
      ring
    rw [hv] at h
    exact mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Complex.I_ne_zero h
  have hmem : zeroRelation ∈ scalarRelations ℂ ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
      (leftAction := NonUnitalModule.zero) :=
    scalarDifference_mem ℂ ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
      (leftAction := NonUnitalModule.zero) Complex.I 1 1
  have hq : zeroComparison zeroRelation = 0 :=
    LinearMap.mem_ker.mp (scalarRelations_le_ker ℂ ℂ ℂ ℂ (rightAction := NonUnitalModule.zero)
      (rightTower := NonUnitalModule.isScalarTower_zero)
      (rightComm := NonUnitalModule.smulCommClass_zero) (leftAction := NonUnitalModule.zero)
      (leftTower := NonUnitalModule.isScalarTower_zero)
      (leftComm := NonUnitalModule.smulCommClass_zero) hmem)
  exact ⟨hne, hmem, hq, fun hinj => hne (hinj (hq.trans (map_zero _).symm)),
    (Submodule.Quotient.mk_eq_zero _).mpr hmem⟩

/-- `TU` is nonzero: the multiplication pairing is balanced for the zero original actions and
for the scalars, so its unitized lift sends `tmul_U 1 1` to `1`. -/
example : zeroUnitizedTmul (1 : ℂ) (1 : ℂ) ≠ 0 := by
  have ha : @NonUnitalModuleTensor.IsBalanced ℂ ℂ ℂ _ _ _ NonUnitalModule.zero
      NonUnitalModule.zero ℂ _ AddMonoidHom.mul := fun a x y => by
    change (0 : ℂ) * y = x * 0
    rw [zero_mul, mul_zero]
  have hc : IsScalarBalanced ℂ (AddMonoidHom.mul : ℂ →+ ℂ →+ ℂ) := fun c x y => by
    simp only [AddMonoidHom.mul_apply, smul_eq_mul]
    ring
  intro h
  have h' := congrArg (unitizedLift ℂ ℂ (rightAction := NonUnitalModule.zero)
    (rightTower := NonUnitalModule.isScalarTower_zero)
    (rightComm := NonUnitalModule.smulCommClass_zero) (leftAction := NonUnitalModule.zero)
    (leftTower := NonUnitalModule.isScalarTower_zero)
    (leftComm := NonUnitalModule.smulCommClass_zero) AddMonoidHom.mul ha hc) h
  rw [unitizedLift_tmul, map_zero, AddMonoidHom.mul_apply, mul_one] at h'
  exact one_ne_zero h'

end ComplexZeroActions

end Examples

end CompatibleUnitizationTensor

end Langlands.Algebra
