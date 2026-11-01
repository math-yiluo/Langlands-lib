import Langlands.Algebra.NondegenerateModuleForgetful
import Langlands.Algebra.IdempotentedRingEndomorphism
import Mathlib.Algebra.Group.ULift

/-!
# Evaluation at the original lifted regular module

Renard I.1.6, printed pp.11–12/PDF17–18. The carrier universe is enlarged
explicitly so that the actual lifted regular object belongs to the category.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra
namespace NondegenerateModuleNaturalEndEvaluation

open CategoryTheory

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

/-- The specified lifted additive group, independent of other chosen structures. -/
@[instance_reducible]
def liftedGroup (A : Type uA) [NonUnitalRing A] : AddCommGroup (ULift.{uM} A) :=
  inferInstance

/-- The original left regular action transported through the actual lift. -/
@[instance_reducible]
def liftedAction (A : Type uA) [NonUnitalRing A] :
    @NonUnitalModule A (ULift.{uM} A) _ (liftedGroup A) where
  smul a m := ULift.up (a * m.down)
  smul_zero a := congrArg ULift.up (mul_zero a)
  smul_add a m n := congrArg ULift.up (mul_add a m.down n.down)
  mul_smul a b m := congrArg ULift.up (mul_assoc a b m.down)
  add_smul a b m := congrArg ULift.up (add_mul a b m.down)
  zero_smul m := congrArg ULift.up (zero_mul m.down)

/-- The original action is nondegenerate by the ring's actual local units. -/
theorem liftedAction_isNondegenerate (hA : IsIdempotented A) :
    @IsNondegenerate A (ULift.{uM} A) _ (liftedGroup A) (liftedAction A) := by
  classical
  intro m
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {m.down}
  exact ⟨e, congrArg ULift.up (he m.down (by simp)).1⟩

/-- The actual lifted regular object in the enlarged original category. -/
def liftedRegularObject (hA : IsIdempotented A) :
    NondegenerateModuleCat.{uA, max uA uM} A :=
  ⟨@NonUnitalModuleCat.of A _ (ULift.{uM} A) (liftedGroup A) (liftedAction A),
    liftedAction_isNondegenerate hA⟩

theorem liftedRegularObject_carrier (hA : IsIdempotented A) :
    ((liftedRegularObject.{uA, uM} hA).obj : Type (max uA uM)) = ULift.{uM} A := rfl

theorem liftedRegularObject_group (hA : IsIdempotented A) :
    (liftedRegularObject.{uA, uM} hA).obj.isAddCommGroup = liftedGroup A := rfl

theorem liftedRegularObject_action (hA : IsIdempotented A) :
    @NonUnitalModuleCat.isModule A _ (liftedRegularObject.{uA, uM} hA).obj =
      liftedAction A := rfl

@[simp] theorem liftedRegularObject_smul (hA : IsIdempotented A)
    (a : A) (m : (liftedRegularObject.{uA, uM} hA).obj) :
    a • m = ULift.up (a * m.down) := rfl

/-- Actual right multiplication, an original intertwiner by associativity. -/
def rightMultiplication (hA : IsIdempotented A) (b : A) :
    liftedRegularObject.{uA, uM} hA ⟶ liftedRegularObject hA :=
  ObjectProperty.homMk
    { toFun m := ULift.up (m.down * b)
      map_zero' := congrArg ULift.up (zero_mul b)
      map_add' m n := congrArg ULift.up (add_mul m.down n.down b)
      map_smul' a m := congrArg ULift.up (mul_assoc a m.down b) }

@[simp] theorem rightMultiplication_apply (hA : IsIdempotented A) (b : A)
    (m : (liftedRegularObject.{uA, uM} hA).obj) :
    (rightMultiplication hA b).hom.toAddMonoidHom m = ULift.up (m.down * b) := rfl

theorem rightMultiplication_coe (hA : IsIdempotented A) (b : A) :
    ((rightMultiplication.{uA, uM} hA b).hom.toAddMonoidHom :
      ULift.{uM} A → ULift.{uM} A) =
      (fun m => ULift.up (m.down * b)) := rfl

/-- The entire additive map is transported original right multiplication. -/
theorem rightMultiplication_hom (hA : IsIdempotented A) (b : A) :
    (rightMultiplication.{uA, uM} hA b).hom.toAddMonoidHom =
      AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mulRight b).comp AddEquiv.ulift.toAddMonoidHom) := rfl

/-- Conjugate the complete additive component through the actual up/down maps. -/
def evaluationEnd (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) : AddMonoid.End A :=
  AddEquiv.ulift.toAddMonoidHom.comp
    ((θ.app (liftedRegularObject hA)).hom.comp AddEquiv.ulift.symm.toAddMonoidHom)

@[simp] theorem evaluationEnd_apply (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (a : A) :
    evaluationEnd hA θ a = (θ.app (liftedRegularObject hA) (ULift.up a)).down := rfl

theorem evaluationEnd_coe (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    (evaluationEnd hA θ : A → A) =
      (fun a => (θ.app (liftedRegularObject hA) (ULift.up a)).down) := rfl

/-- Naturality with the actual right multiplication gives the full map identity. -/
theorem evaluationEnd_comp_right (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (b : A) :
    (evaluationEnd hA θ).comp (AddMonoidHom.mulRight b) =
      (AddMonoidHom.mulRight b).comp (evaluationEnd hA θ) := by
  apply AddMonoidHom.ext
  intro a
  have h := congrArg (fun f => (f (ULift.up a)).down)
    (θ.naturality (rightMultiplication hA b))
  exact h

/-- The right-linearity equation is derived, not supplied as a certificate. -/
theorem evaluationEnd_apply_mul (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (a b : A) :
    evaluationEnd hA θ (a * b) = evaluationEnd hA θ a * b :=
  congrArg (fun f : AddMonoid.End A => f a) (evaluationEnd_comp_right hA θ b)

/-- Evaluation lands in the existing actual right-linear endomorphism subring. -/
def evaluationRightLinear (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    IdempotentedRingEndomorphism.RightLinearEnd A :=
  ⟨evaluationEnd hA θ, evaluationEnd_apply_mul hA θ⟩

@[simp] theorem evaluationRightLinear_val (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    (evaluationRightLinear hA θ).val = evaluationEnd hA θ := rfl

/-- The packaged element retains the naturality-derived right-linearity equation. -/
theorem evaluationRightLinear_apply_mul (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (a b : A) :
    (evaluationRightLinear hA θ).val (a * b) = (evaluationRightLinear hA θ).val a * b :=
  evaluationEnd_apply_mul hA θ a b

/-- Evaluation into all additive endomorphisms, before restricting the codomain. -/
def toEndRingHom (hA : IsIdempotented A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+* AddMonoid.End A := by
  letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  exact
    { toFun := evaluationEnd hA
      map_zero' := by apply AddMonoidHom.ext; intro a; rfl
      map_one' := by apply AddMonoidHom.ext; intro a; rfl
      map_add' := by intro θ η; apply AddMonoidHom.ext; intro a; rfl
      map_mul' := by intro θ η; apply AddMonoidHom.ext; intro a; rfl }

@[simp] theorem toEndRingHom_apply (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    toEndRingHom hA θ = evaluationEnd hA θ := rfl

theorem toEndRingHom_coe (hA : IsIdempotented A) :
    (toEndRingHom.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      AddMonoid.End A) = evaluationEnd hA := rfl

/-- Source and target products both apply the right factor first. -/
theorem evaluationEnd_mul (hA : IsIdempotented A)
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    evaluationEnd hA (θ * η) = (evaluationEnd hA θ).comp (evaluationEnd hA η) := rfl

/-- Actual evaluation as a unital ring map, with left-after-right composition. -/
def toRightLinearEnd (hA : IsIdempotented A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+*
      IdempotentedRingEndomorphism.RightLinearEnd A := by
  letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  exact
    { toFun := evaluationRightLinear hA
      map_zero' := by apply Subtype.ext; apply AddMonoidHom.ext; intro a; rfl
      map_one' := by apply Subtype.ext; apply AddMonoidHom.ext; intro a; rfl
      map_add' := by intro θ η; apply Subtype.ext; apply AddMonoidHom.ext; intro a; rfl
      map_mul' := by intro θ η; apply Subtype.ext; apply AddMonoidHom.ext; intro a; rfl }

@[simp] theorem toRightLinearEnd_apply (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    toRightLinearEnd hA θ = evaluationRightLinear hA θ := rfl

@[simp] theorem toRightLinearEnd_val (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    (toRightLinearEnd hA θ).val = evaluationEnd hA θ := rfl

theorem toRightLinearEnd_coe (hA : IsIdempotented A) :
    (toRightLinearEnd.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      IdempotentedRingEndomorphism.RightLinearEnd A) = evaluationRightLinear hA := rfl

theorem toRightLinearEnd_val_coe (hA : IsIdempotented A) :
    (fun θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A =>
      (toRightLinearEnd hA θ).val) = evaluationEnd hA := rfl

@[simp] theorem toRightLinearEnd_apply_apply (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (a : A) :
    (toRightLinearEnd hA θ).val a =
      (θ.app (liftedRegularObject hA) (ULift.up a)).down := rfl

/-- Equality of the entire bundled ring map after actual subtype inclusion. -/
theorem toRightLinearEnd_subtype_comp (hA : IsIdempotented A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    (IdempotentedRingEndomorphism.rightLinearEnd A).subtype.comp
      (toRightLinearEnd.{uA, uM} hA) = toEndRingHom hA := rfl

/-- The image's right-linearity is the equation derived from naturality. -/
theorem toRightLinearEnd_val_apply_mul (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (a b : A) :
    (toRightLinearEnd hA θ).val (a * b) = (toRightLinearEnd hA θ).val a * b :=
  evaluationEnd_apply_mul hA θ a b

/-- The target product applies the image of the right factor first. -/
theorem toRightLinearEnd_mul_apply (hA : IsIdempotented A)
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (a : A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    (toRightLinearEnd hA (θ * η)).val a =
      (toRightLinearEnd hA θ).val ((toRightLinearEnd hA η).val a) := rfl

/-- The complete conjugation identity, as an equality of additive maps. -/
theorem evaluationEnd_eq_comp (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    evaluationEnd hA θ = AddEquiv.ulift.toAddMonoidHom.comp
      ((θ.app (liftedRegularObject hA)).hom.comp AddEquiv.ulift.symm.toAddMonoidHom) := rfl

/-- The actual additive composite with the published idempotent evaluation. -/
def familyAddHom (hA : IsIdempotented A) :
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+ IdempotentedRingRightLimit A :=
  IdempotentedRingEndomorphism.idempotentEvaluation.comp
    (toRightLinearEnd hA).toAddMonoidHom

theorem familyAddHom_eq_comp (hA : IsIdempotented A) :
    familyAddHom.{uA, uM} hA =
      IdempotentedRingEndomorphism.idempotentEvaluation.comp
        (toRightLinearEnd hA).toAddMonoidHom := rfl

theorem familyAddHom_coe (hA : IsIdempotented A) :
    (familyAddHom.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      IdempotentedRingRightLimit A) =
      (fun θ => IdempotentedRingEndomorphism.idempotentEvaluation
        (evaluationRightLinear hA θ)) := rfl

@[simp] theorem familyAddHom_val (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (e : Idempotent A) :
    (familyAddHom hA θ).val e =
      (θ.app (liftedRegularObject hA) (ULift.up (e : A))).down := rfl

/-- The complete coordinate function retains the actual evaluated component. -/
theorem familyAddHom_val_coe (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    (familyAddHom hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject hA) (ULift.up (e : A))).down) := rfl

@[simp] theorem familyAddHom_one (hA : IsIdempotented A) :
    familyAddHom.{uA, uM} hA 1 = IdempotentedRingRightLimit.unit := by
  apply Subtype.ext
  funext e
  rfl

/-- Right-linearity gives the family product directly, without classification. -/
theorem familyAddHom_mul (hA : IsIdempotented A)
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    familyAddHom hA (θ * η) = IdempotentedRingRightLimit.product hA
      (familyAddHom hA θ) (familyAddHom hA η) := by
  classical
  apply Subtype.ext
  funext e
  obtain ⟨f, hf⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA)
    {(familyAddHom hA η).val e}
  have hfix : (f : A) * (familyAddHom hA η).val e = (familyAddHom hA η).val e :=
    (hf _ (Finset.mem_singleton.mpr rfl)).1
  rw [IdempotentedRingRightLimit.product_val hA _ _ e f hfix]
  change evaluationEnd hA θ (evaluationEnd hA η (e : A)) =
    evaluationEnd hA θ (f : A) * evaluationEnd hA η (e : A)
  calc
    evaluationEnd hA θ (evaluationEnd hA η (e : A)) =
        evaluationEnd hA θ ((f : A) * evaluationEnd hA η (e : A)) :=
      congrArg (evaluationEnd hA θ) hfix.symm
    _ = _ := evaluationEnd_apply_mul hA θ (f : A) (evaluationEnd hA η (e : A))

/-- Evaluation as an actual unital ring map to the specified compatible-family ring. -/
def toFamilyRingHom (hA : IsIdempotented A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+* IdempotentedRingRightLimit A := by
  letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  letI := IdempotentedRingRightLimit.ring hA
  exact
    { toFun := familyAddHom hA
      map_zero' := (familyAddHom hA).map_zero
      map_add' := (familyAddHom hA).map_add
      map_one' := familyAddHom_one hA
      map_mul' := familyAddHom_mul hA }

@[simp] theorem toFamilyRingHom_apply (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    toFamilyRingHom hA θ = familyAddHom hA θ := rfl

theorem toFamilyRingHom_coe (hA : IsIdempotented A) :
    (toFamilyRingHom.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      IdempotentedRingRightLimit A) = familyAddHom hA := rfl

/-- Equality of the entire additive projection with the specified composite. -/
theorem toFamilyRingHom_toAddMonoidHom (hA : IsIdempotented A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    (toFamilyRingHom.{uA, uM} hA).toAddMonoidHom =
      IdempotentedRingEndomorphism.idempotentEvaluation.comp
        (toRightLinearEnd hA).toAddMonoidHom := rfl

@[simp] theorem toFamilyRingHom_val (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) (e : Idempotent A) :
    (toFamilyRingHom hA θ).val e =
      (θ.app (liftedRegularObject hA) (ULift.up (e : A))).down := rfl

theorem toFamilyRingHom_val_coe (hA : IsIdempotented A)
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    (toFamilyRingHom hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject hA) (ULift.up (e : A))).down) := rfl

/-! Complete unapplied interfaces at independent scalar and lifting universes. -/

example : (A : Type uA) → [NonUnitalRing A] → AddCommGroup (ULift.{uM} A) :=
  @liftedGroup.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    @NonUnitalModule A (ULift.{uM} A) _ (liftedGroup.{uA, uM} A) :=
  @liftedAction.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @IsNondegenerate A (ULift.{uM} A) _ (liftedGroup.{uA, uM} A) (liftedAction.{uA, uM} A) :=
  @liftedAction_isNondegenerate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleCat.{uA, max uA uM} A :=
  @liftedRegularObject.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    ((liftedRegularObject.{uA, uM} hA).obj : Type (max uA uM)) = ULift.{uM} A :=
  @liftedRegularObject_carrier.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (liftedRegularObject.{uA, uM} hA).obj.isAddCommGroup = liftedGroup.{uA, uM} A :=
  @liftedRegularObject_group.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @NonUnitalModuleCat.isModule A _ (liftedRegularObject.{uA, uM} hA).obj =
      liftedAction.{uA, uM} A :=
  @liftedRegularObject_action.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (m : (liftedRegularObject.{uA, uM} hA).obj) →
    a • m = ULift.up (a * m.down) :=
  @liftedRegularObject_smul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) → A →
    (liftedRegularObject.{uA, uM} hA ⟶ liftedRegularObject.{uA, uM} hA) :=
  @rightMultiplication.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) → (b : A) →
    ((rightMultiplication.{uA, uM} hA b).hom.toAddMonoidHom :
      ULift.{uM} A → ULift.{uM} A) = (fun m => ULift.up (m.down * b)) :=
  @rightMultiplication_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) → (b : A) →
    (rightMultiplication.{uA, uM} hA b).hom.toAddMonoidHom =
      AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mulRight b).comp AddEquiv.ulift.toAddMonoidHom) :=
  @rightMultiplication_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A → AddMonoid.End A :=
  @evaluationEnd.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    (evaluationEnd.{uA, uM} hA θ : A → A) =
      (fun a => (θ.app (liftedRegularObject.{uA, uM} hA) (ULift.up a)).down) :=
  @evaluationEnd_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    evaluationEnd.{uA, uM} hA θ = AddEquiv.ulift.toAddMonoidHom.comp
      ((θ.app (liftedRegularObject.{uA, uM} hA)).hom.comp AddEquiv.ulift.symm.toAddMonoidHom) :=
  @evaluationEnd_eq_comp.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (b : A) →
    (evaluationEnd.{uA, uM} hA θ).comp (AddMonoidHom.mulRight b) =
      (AddMonoidHom.mulRight b).comp (evaluationEnd.{uA, uM} hA θ) :=
  @evaluationEnd_comp_right.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (a b : A) →
    evaluationEnd.{uA, uM} hA θ (a * b) = evaluationEnd.{uA, uM} hA θ a * b :=
  @evaluationEnd_apply_mul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
    IdempotentedRingEndomorphism.RightLinearEnd A :=
  @evaluationRightLinear.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    (evaluationRightLinear.{uA, uM} hA θ).val = evaluationEnd.{uA, uM} hA θ :=
  @evaluationRightLinear_val.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (a b : A) →
    (evaluationRightLinear.{uA, uM} hA θ).val (a * b) =
      (evaluationRightLinear.{uA, uM} hA θ).val a * b :=
  @evaluationRightLinear_apply_mul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+* AddMonoid.End A :=
  @toEndRingHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toEndRingHom.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      AddMonoid.End A) = evaluationEnd.{uA, uM} hA :=
  @toEndRingHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    evaluationEnd.{uA, uM} hA (θ * η) =
      (evaluationEnd.{uA, uM} hA θ).comp (evaluationEnd.{uA, uM} hA η) :=
  @evaluationEnd_mul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+*
      IdempotentedRingEndomorphism.RightLinearEnd A :=
  @toRightLinearEnd.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toRightLinearEnd.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      IdempotentedRingEndomorphism.RightLinearEnd A) = evaluationRightLinear.{uA, uM} hA :=
  @toRightLinearEnd_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (fun θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A =>
      (toRightLinearEnd.{uA, uM} hA θ).val) = evaluationEnd.{uA, uM} hA :=
  @toRightLinearEnd_val_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (a : A) →
    (toRightLinearEnd.{uA, uM} hA θ).val a =
      (θ.app (liftedRegularObject.{uA, uM} hA) (ULift.up a)).down :=
  @toRightLinearEnd_apply_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    (IdempotentedRingEndomorphism.rightLinearEnd A).subtype.comp
      (toRightLinearEnd.{uA, uM} hA) = toEndRingHom.{uA, uM} hA :=
  @toRightLinearEnd_subtype_comp.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (a b : A) →
    (toRightLinearEnd.{uA, uM} hA θ).val (a * b) =
      (toRightLinearEnd.{uA, uM} hA θ).val a * b :=
  @toRightLinearEnd_val_apply_mul.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (a : A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    (toRightLinearEnd.{uA, uM} hA (θ * η)).val a =
      (toRightLinearEnd.{uA, uM} hA θ).val ((toRightLinearEnd.{uA, uM} hA η).val a) :=
  @toRightLinearEnd_mul_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    (NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+ IdempotentedRingRightLimit A) :=
  @familyAddHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    familyAddHom.{uA, uM} hA = IdempotentedRingEndomorphism.idempotentEvaluation.comp
      (toRightLinearEnd.{uA, uM} hA).toAddMonoidHom :=
  @familyAddHom_eq_comp.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (familyAddHom.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      IdempotentedRingRightLimit A) =
      (fun θ => IdempotentedRingEndomorphism.idempotentEvaluation
        (evaluationRightLinear.{uA, uM} hA θ)) :=
  @familyAddHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    (familyAddHom.{uA, uM} hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject.{uA, uM} hA) (ULift.up (e : A))).down) :=
  @familyAddHom_val_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+* IdempotentedRingRightLimit A :=
  @toFamilyRingHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toFamilyRingHom.{uA, uM} hA : NondegenerateModuleNaturalEnd.{uA, max uA uM} A →
      IdempotentedRingRightLimit A) = familyAddHom.{uA, uM} hA :=
  @toFamilyRingHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    (toFamilyRingHom.{uA, uM} hA).toAddMonoidHom =
      IdempotentedRingEndomorphism.idempotentEvaluation.comp
        (toRightLinearEnd.{uA, uM} hA).toAddMonoidHom :=
  @toFamilyRingHom_toAddMonoidHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    (toFamilyRingHom.{uA, uM} hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject.{uA, uM} hA) (ULift.up (e : A))).down) :=
  @toFamilyRingHom_val_coe.{uA, uM}

/-! Complete unapplied interfaces at (uA,uM)=(0,1); the category uses max 0 1. -/

example : (A : Type 0) → [NonUnitalRing A] → AddCommGroup (ULift.{1} A) :=
  @liftedGroup.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    @NonUnitalModule A (ULift.{1} A) _ (liftedGroup.{0, 1} A) :=
  @liftedAction.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @IsNondegenerate A (ULift.{1} A) _ (liftedGroup.{0, 1} A) (liftedAction.{0, 1} A) :=
  @liftedAction_isNondegenerate.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleCat.{0, max 0 1} A :=
  @liftedRegularObject.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    ((liftedRegularObject.{0, 1} hA).obj : Type (max 0 1)) = ULift.{1} A :=
  @liftedRegularObject_carrier.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (liftedRegularObject.{0, 1} hA).obj.isAddCommGroup = liftedGroup.{0, 1} A :=
  @liftedRegularObject_group.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @NonUnitalModuleCat.isModule A _ (liftedRegularObject.{0, 1} hA).obj =
      liftedAction.{0, 1} A :=
  @liftedRegularObject_action.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (m : (liftedRegularObject.{0, 1} hA).obj) →
    a • m = ULift.up (a * m.down) :=
  @liftedRegularObject_smul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) → A →
    (liftedRegularObject.{0, 1} hA ⟶ liftedRegularObject.{0, 1} hA) :=
  @rightMultiplication.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) → (b : A) →
    ((rightMultiplication.{0, 1} hA b).hom.toAddMonoidHom :
      ULift.{1} A → ULift.{1} A) = (fun m => ULift.up (m.down * b)) :=
  @rightMultiplication_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) → (b : A) →
    (rightMultiplication.{0, 1} hA b).hom.toAddMonoidHom =
      AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mulRight b).comp AddEquiv.ulift.toAddMonoidHom) :=
  @rightMultiplication_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleNaturalEnd.{0, max 0 1} A → AddMonoid.End A :=
  @evaluationEnd.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) →
    (evaluationEnd.{0, 1} hA θ : A → A) =
      (fun a => (θ.app (liftedRegularObject.{0, 1} hA) (ULift.up a)).down) :=
  @evaluationEnd_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) →
    evaluationEnd.{0, 1} hA θ = AddEquiv.ulift.toAddMonoidHom.comp
      ((θ.app (liftedRegularObject.{0, 1} hA)).hom.comp AddEquiv.ulift.symm.toAddMonoidHom) :=
  @evaluationEnd_eq_comp.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) → (b : A) →
    (evaluationEnd.{0, 1} hA θ).comp (AddMonoidHom.mulRight b) =
      (AddMonoidHom.mulRight b).comp (evaluationEnd.{0, 1} hA θ) :=
  @evaluationEnd_comp_right.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) → (a b : A) →
    evaluationEnd.{0, 1} hA θ (a * b) = evaluationEnd.{0, 1} hA θ a * b :=
  @evaluationEnd_apply_mul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleNaturalEnd.{0, max 0 1} A →
    IdempotentedRingEndomorphism.RightLinearEnd A :=
  @evaluationRightLinear.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) →
    (evaluationRightLinear.{0, 1} hA θ).val = evaluationEnd.{0, 1} hA θ :=
  @evaluationRightLinear_val.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) → (a b : A) →
    (evaluationRightLinear.{0, 1} hA θ).val (a * b) =
      (evaluationRightLinear.{0, 1} hA θ).val a * b :=
  @evaluationRightLinear_apply_mul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    NondegenerateModuleNaturalEnd.{0, max 0 1} A →+* AddMonoid.End A :=
  @toEndRingHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toEndRingHom.{0, 1} hA : NondegenerateModuleNaturalEnd.{0, max 0 1} A →
      AddMonoid.End A) = evaluationEnd.{0, 1} hA :=
  @toEndRingHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{0, max 0 1} A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    evaluationEnd.{0, 1} hA (θ * η) =
      (evaluationEnd.{0, 1} hA θ).comp (evaluationEnd.{0, 1} hA η) :=
  @evaluationEnd_mul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    NondegenerateModuleNaturalEnd.{0, max 0 1} A →+*
      IdempotentedRingEndomorphism.RightLinearEnd A :=
  @toRightLinearEnd.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toRightLinearEnd.{0, 1} hA : NondegenerateModuleNaturalEnd.{0, max 0 1} A →
      IdempotentedRingEndomorphism.RightLinearEnd A) = evaluationRightLinear.{0, 1} hA :=
  @toRightLinearEnd_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (fun θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A =>
      (toRightLinearEnd.{0, 1} hA θ).val) = evaluationEnd.{0, 1} hA :=
  @toRightLinearEnd_val_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) → (a : A) →
    (toRightLinearEnd.{0, 1} hA θ).val a =
      (θ.app (liftedRegularObject.{0, 1} hA) (ULift.up a)).down :=
  @toRightLinearEnd_apply_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    (IdempotentedRingEndomorphism.rightLinearEnd A).subtype.comp
      (toRightLinearEnd.{0, 1} hA) = toEndRingHom.{0, 1} hA :=
  @toRightLinearEnd_subtype_comp.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) → (a b : A) →
    (toRightLinearEnd.{0, 1} hA θ).val (a * b) =
      (toRightLinearEnd.{0, 1} hA θ).val a * b :=
  @toRightLinearEnd_val_apply_mul.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{0, max 0 1} A) → (a : A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    (toRightLinearEnd.{0, 1} hA (θ * η)).val a =
      (toRightLinearEnd.{0, 1} hA θ).val ((toRightLinearEnd.{0, 1} hA η).val a) :=
  @toRightLinearEnd_mul_apply.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    (NondegenerateModuleNaturalEnd.{0, max 0 1} A →+ IdempotentedRingRightLimit A) :=
  @familyAddHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    familyAddHom.{0, 1} hA = IdempotentedRingEndomorphism.idempotentEvaluation.comp
      (toRightLinearEnd.{0, 1} hA).toAddMonoidHom :=
  @familyAddHom_eq_comp.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (familyAddHom.{0, 1} hA : NondegenerateModuleNaturalEnd.{0, max 0 1} A →
      IdempotentedRingRightLimit A) =
      (fun θ => IdempotentedRingEndomorphism.idempotentEvaluation
        (evaluationRightLinear.{0, 1} hA θ)) :=
  @familyAddHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) →
    (familyAddHom.{0, 1} hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject.{0, 1} hA) (ULift.up (e : A))).down) :=
  @familyAddHom_val_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    letI := IdempotentedRingRightLimit.ring hA
    NondegenerateModuleNaturalEnd.{0, max 0 1} A →+* IdempotentedRingRightLimit A :=
  @toFamilyRingHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toFamilyRingHom.{0, 1} hA : NondegenerateModuleNaturalEnd.{0, max 0 1} A →
      IdempotentedRingRightLimit A) = familyAddHom.{0, 1} hA :=
  @toFamilyRingHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{0, max 0 1} A
    letI := IdempotentedRingRightLimit.ring hA
    (toFamilyRingHom.{0, 1} hA).toAddMonoidHom =
      IdempotentedRingEndomorphism.idempotentEvaluation.comp
        (toRightLinearEnd.{0, 1} hA).toAddMonoidHom :=
  @toFamilyRingHom_toAddMonoidHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{0, max 0 1} A) →
    (toFamilyRingHom.{0, 1} hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject.{0, 1} hA) (ULift.up (e : A))).down) :=
  @toFamilyRingHom_val_coe.{0, 1}

/-! Complete unapplied interfaces at (uA,uM)=(1,0); the category uses max 1 0. -/

example : (A : Type 1) → [NonUnitalRing A] → AddCommGroup (ULift.{0} A) :=
  @liftedGroup.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    @NonUnitalModule A (ULift.{0} A) _ (liftedGroup.{1, 0} A) :=
  @liftedAction.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @IsNondegenerate A (ULift.{0} A) _ (liftedGroup.{1, 0} A) (liftedAction.{1, 0} A) :=
  @liftedAction_isNondegenerate.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleCat.{1, max 1 0} A :=
  @liftedRegularObject.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    ((liftedRegularObject.{1, 0} hA).obj : Type (max 1 0)) = ULift.{0} A :=
  @liftedRegularObject_carrier.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (liftedRegularObject.{1, 0} hA).obj.isAddCommGroup = liftedGroup.{1, 0} A :=
  @liftedRegularObject_group.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    @NonUnitalModuleCat.isModule A _ (liftedRegularObject.{1, 0} hA).obj =
      liftedAction.{1, 0} A :=
  @liftedRegularObject_action.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (m : (liftedRegularObject.{1, 0} hA).obj) →
    a • m = ULift.up (a * m.down) :=
  @liftedRegularObject_smul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) → A →
    (liftedRegularObject.{1, 0} hA ⟶ liftedRegularObject.{1, 0} hA) :=
  @rightMultiplication.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) → (b : A) →
    ((rightMultiplication.{1, 0} hA b).hom.toAddMonoidHom :
      ULift.{0} A → ULift.{0} A) = (fun m => ULift.up (m.down * b)) :=
  @rightMultiplication_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) → (b : A) →
    (rightMultiplication.{1, 0} hA b).hom.toAddMonoidHom =
      AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mulRight b).comp AddEquiv.ulift.toAddMonoidHom) :=
  @rightMultiplication_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleNaturalEnd.{1, max 1 0} A → AddMonoid.End A :=
  @evaluationEnd.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) →
    (evaluationEnd.{1, 0} hA θ : A → A) =
      (fun a => (θ.app (liftedRegularObject.{1, 0} hA) (ULift.up a)).down) :=
  @evaluationEnd_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) →
    evaluationEnd.{1, 0} hA θ = AddEquiv.ulift.toAddMonoidHom.comp
      ((θ.app (liftedRegularObject.{1, 0} hA)).hom.comp AddEquiv.ulift.symm.toAddMonoidHom) :=
  @evaluationEnd_eq_comp.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) → (b : A) →
    (evaluationEnd.{1, 0} hA θ).comp (AddMonoidHom.mulRight b) =
      (AddMonoidHom.mulRight b).comp (evaluationEnd.{1, 0} hA θ) :=
  @evaluationEnd_comp_right.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) → (a b : A) →
    evaluationEnd.{1, 0} hA θ (a * b) = evaluationEnd.{1, 0} hA θ a * b :=
  @evaluationEnd_apply_mul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    NondegenerateModuleNaturalEnd.{1, max 1 0} A →
    IdempotentedRingEndomorphism.RightLinearEnd A :=
  @evaluationRightLinear.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) →
    (evaluationRightLinear.{1, 0} hA θ).val = evaluationEnd.{1, 0} hA θ :=
  @evaluationRightLinear_val.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) → (a b : A) →
    (evaluationRightLinear.{1, 0} hA θ).val (a * b) =
      (evaluationRightLinear.{1, 0} hA θ).val a * b :=
  @evaluationRightLinear_apply_mul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    NondegenerateModuleNaturalEnd.{1, max 1 0} A →+* AddMonoid.End A :=
  @toEndRingHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toEndRingHom.{1, 0} hA : NondegenerateModuleNaturalEnd.{1, max 1 0} A →
      AddMonoid.End A) = evaluationEnd.{1, 0} hA :=
  @toEndRingHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{1, max 1 0} A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    evaluationEnd.{1, 0} hA (θ * η) =
      (evaluationEnd.{1, 0} hA θ).comp (evaluationEnd.{1, 0} hA η) :=
  @evaluationEnd_mul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    NondegenerateModuleNaturalEnd.{1, max 1 0} A →+*
      IdempotentedRingEndomorphism.RightLinearEnd A :=
  @toRightLinearEnd.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toRightLinearEnd.{1, 0} hA : NondegenerateModuleNaturalEnd.{1, max 1 0} A →
      IdempotentedRingEndomorphism.RightLinearEnd A) = evaluationRightLinear.{1, 0} hA :=
  @toRightLinearEnd_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (fun θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A =>
      (toRightLinearEnd.{1, 0} hA θ).val) = evaluationEnd.{1, 0} hA :=
  @toRightLinearEnd_val_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) → (a : A) →
    (toRightLinearEnd.{1, 0} hA θ).val a =
      (θ.app (liftedRegularObject.{1, 0} hA) (ULift.up a)).down :=
  @toRightLinearEnd_apply_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    (IdempotentedRingEndomorphism.rightLinearEnd A).subtype.comp
      (toRightLinearEnd.{1, 0} hA) = toEndRingHom.{1, 0} hA :=
  @toRightLinearEnd_subtype_comp.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) → (a b : A) →
    (toRightLinearEnd.{1, 0} hA θ).val (a * b) =
      (toRightLinearEnd.{1, 0} hA θ).val a * b :=
  @toRightLinearEnd_val_apply_mul.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{1, max 1 0} A) → (a : A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    (toRightLinearEnd.{1, 0} hA (θ * η)).val a =
      (toRightLinearEnd.{1, 0} hA θ).val ((toRightLinearEnd.{1, 0} hA η).val a) :=
  @toRightLinearEnd_mul_apply.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    (NondegenerateModuleNaturalEnd.{1, max 1 0} A →+ IdempotentedRingRightLimit A) :=
  @familyAddHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    familyAddHom.{1, 0} hA = IdempotentedRingEndomorphism.idempotentEvaluation.comp
      (toRightLinearEnd.{1, 0} hA).toAddMonoidHom :=
  @familyAddHom_eq_comp.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (familyAddHom.{1, 0} hA : NondegenerateModuleNaturalEnd.{1, max 1 0} A →
      IdempotentedRingRightLimit A) =
      (fun θ => IdempotentedRingEndomorphism.idempotentEvaluation
        (evaluationRightLinear.{1, 0} hA θ)) :=
  @familyAddHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) →
    (familyAddHom.{1, 0} hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject.{1, 0} hA) (ULift.up (e : A))).down) :=
  @familyAddHom_val_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    letI := IdempotentedRingRightLimit.ring hA
    NondegenerateModuleNaturalEnd.{1, max 1 0} A →+* IdempotentedRingRightLimit A :=
  @toFamilyRingHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (toFamilyRingHom.{1, 0} hA : NondegenerateModuleNaturalEnd.{1, max 1 0} A →
      IdempotentedRingRightLimit A) = familyAddHom.{1, 0} hA :=
  @toFamilyRingHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{1, max 1 0} A
    letI := IdempotentedRingRightLimit.ring hA
    (toFamilyRingHom.{1, 0} hA).toAddMonoidHom =
      IdempotentedRingEndomorphism.idempotentEvaluation.comp
        (toRightLinearEnd.{1, 0} hA).toAddMonoidHom :=
  @toFamilyRingHom_toAddMonoidHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{1, max 1 0} A) →
    (toFamilyRingHom.{1, 0} hA θ).val =
      (fun e : Idempotent A => (θ.app (liftedRegularObject.{1, 0} hA) (ULift.up (e : A))).down) :=
  @toFamilyRingHom_val_coe.{1, 0}

/-! Named original scalar choices remain explicit in the presence of another ring. -/
section CompetingOriginalRings

variable {A : Type uA} (originalRing : NonUnitalRing A)
  [competingOriginalRing : NonUnitalRing A]

example : (hA : @IsIdempotented A originalRing) →
    ((@liftedRegularObject.{uA, uM} A originalRing hA).obj : Type (max uA uM)) =
      ULift.{uM} A :=
  @liftedRegularObject_carrier.{uA, uM} A originalRing

example : (hA : @IsIdempotented A originalRing) →
    @NonUnitalModuleCat.isAddCommGroup A originalRing
      (@liftedRegularObject.{uA, uM} A originalRing hA).obj =
      @liftedGroup.{uA, uM} A originalRing :=
  @liftedRegularObject_group.{uA, uM} A originalRing

example : (hA : @IsIdempotented A originalRing) →
    @NonUnitalModuleCat.isModule A originalRing
      (@liftedRegularObject.{uA, uM} A originalRing hA).obj =
      @liftedAction.{uA, uM} A originalRing :=
  @liftedRegularObject_action.{uA, uM} A originalRing

example (a : A) (m : ULift.{uM} A) :
    @SMul.smul A (ULift.{uM} A)
      (@liftedAction.{uA, uM} A originalRing).toDistribSMul.toSMul a m =
      ULift.up (@Mul.mul A originalRing.toMul a m.down) := rfl

example (hA : @IsIdempotented A originalRing)
    (θ : @NondegenerateModuleNaturalEnd.{uA, max uA uM} A originalRing) :
    (@evaluationEnd.{uA, uM} A originalRing hA θ : A → A) =
      (fun a => (θ.app (@liftedRegularObject.{uA, uM} A originalRing hA)
        (ULift.up a)).down) :=
  @evaluationEnd_coe.{uA, uM} A originalRing hA θ

end CompetingOriginalRings

/-! The lifted object's specified group and action survive same-carrier alternatives. -/
section CompetingLiftedStructures

variable {A : Type uA} [NonUnitalRing A]
  [competingLiftedGroup : AddCommGroup (ULift.{uM} A)]
  [competingLiftedAction : @NonUnitalModule A (ULift.{uM} A) _ competingLiftedGroup]

example : (hA : IsIdempotented A) →
    (liftedRegularObject.{uA, uM} hA).obj.isAddCommGroup = liftedGroup.{uA, uM} A :=
  @liftedRegularObject_group.{uA, uM} A _

example : (hA : IsIdempotented A) →
    @NonUnitalModuleCat.isModule A _ (liftedRegularObject.{uA, uM} hA).obj =
      liftedAction.{uA, uM} A :=
  @liftedRegularObject_action.{uA, uM} A _

example (a : A) (m : ULift.{uM} A) :
    @SMul.smul A (ULift.{uM} A)
      (liftedAction.{uA, uM} A).toDistribSMul.toSMul a m =
      ULift.up (a * m.down) := rfl

example : (hA : IsIdempotented A) → (b : A) →
    letI := liftedGroup.{uA, uM} A
    (rightMultiplication.{uA, uM} hA b).hom.toAddMonoidHom =
      AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mulRight b).comp AddEquiv.ulift.toAddMonoidHom) :=
  @rightMultiplication_hom.{uA, uM} A _

end CompetingLiftedStructures

/-! The two ring maps always use the named source ring and named family ring. -/
section CompetingEndAndFamilyRings

variable {A : Type uA} [NonUnitalRing A]
  [competingEndRing : Ring (NondegenerateModuleNaturalEnd.{uA, max uA uM} A)]
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]

example : (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+*
      IdempotentedRingEndomorphism.RightLinearEnd A :=
  @toRightLinearEnd.{uA, uM} A _

example : (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    (IdempotentedRingEndomorphism.rightLinearEnd A).subtype.comp
      (toRightLinearEnd.{uA, uM} hA) = toEndRingHom.{uA, uM} hA :=
  @toRightLinearEnd_subtype_comp.{uA, uM} A _

example : (hA : IsIdempotented A) →
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) → (a : A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    (toRightLinearEnd.{uA, uM} hA (θ * η)).val a =
      (toRightLinearEnd.{uA, uM} hA θ).val ((toRightLinearEnd.{uA, uM} hA η).val a) :=
  @toRightLinearEnd_mul_apply.{uA, uM} A _

example : (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    NondegenerateModuleNaturalEnd.{uA, max uA uM} A →+* IdempotentedRingRightLimit A :=
  @toFamilyRingHom.{uA, uM} A _

example : (hA : IsIdempotented A) →
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    (toFamilyRingHom.{uA, uM} hA).toAddMonoidHom =
      IdempotentedRingEndomorphism.idempotentEvaluation.comp
        (toRightLinearEnd.{uA, uM} hA).toAddMonoidHom :=
  @toFamilyRingHom_toAddMonoidHom.{uA, uM} A _

example (hA : IsIdempotented A)
    (θ η : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) :
    letI := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
    letI := IdempotentedRingRightLimit.ring hA
    toFamilyRingHom.{uA, uM} hA (θ * η) =
      toFamilyRingHom.{uA, uM} hA θ * toFamilyRingHom.{uA, uM} hA η := by
  let _ := NondegenerateModuleNaturalEnd.ring.{uA, max uA uM} A
  let _ := IdempotentedRingRightLimit.ring hA
  exact (toFamilyRingHom.{uA, uM} hA).map_mul θ η

example : (hA : IsIdempotented A) →
    (θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A) →
    (toFamilyRingHom.{uA, uM} hA θ).val =
      (fun e : Idempotent A =>
        (θ.app (liftedRegularObject.{uA, uM} hA) (ULift.up (e : A))).down) :=
  @toFamilyRingHom_val_coe.{uA, uM} A _

end CompetingEndAndFamilyRings

/-! A zero scalar ring gives an actual zero lifted carrier and zero evaluated maps. -/
section SubsingletonRing

variable {A : Type uA} [NonUnitalRing A] [Subsingleton A]

example (a : A) (m : ULift.{uM} A) :
    @SMul.smul A (ULift.{uM} A)
      (liftedAction.{uA, uM} A).toDistribSMul.toSMul a m = 0 :=
  Subsingleton.elim _ _

example : ∃ hA : IsIdempotented A,
    ∀ θ : NondegenerateModuleNaturalEnd.{uA, max uA uM} A,
      evaluationEnd.{uA, uM} hA θ = 0 ∧ toFamilyRingHom.{uA, uM} hA θ = 0 := by
  have hA : IsIdempotented A := by
    intro s
    refine ⟨⟨0, zero_mul 0⟩, ?_⟩
    intro a _ha
    exact Subsingleton.elim _ _
  refine ⟨hA, ?_⟩
  intro θ
  constructor
  · apply AddMonoidHom.ext
    intro a
    exact Subsingleton.elim _ _
  · apply Subtype.ext
    funext e
    exact Subsingleton.elim _ _

end SubsingletonRing

end NondegenerateModuleNaturalEndEvaluation
end Langlands.Algebra
