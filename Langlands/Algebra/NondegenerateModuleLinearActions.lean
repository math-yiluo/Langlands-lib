import Langlands.Algebra.NondegenerateScalars
import Langlands.Algebra.IdempotentedRingRightLimitAction
import Langlands.Algebra.NondegenerateModuleForgetful
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Module.Pi

/-!
# Simultaneous original and completed linear actions

The maps of Renard I.1.8.2 on the original carriers, with canonical scalars
from I.2.1. The coefficient semiring and arbitrary indexed family are internal
generalizations of the complex simple-module setting.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NondegenerateModuleLinearActions

universe uK uA uI uM

section Individual

variable (k : Type uK) {A : Type uA} {M : Type uM}
  [CommSemiring k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The actual linear endomorphisms for the canonical scalars on the original group. -/
abbrev End : Type uM :=
  letI := NondegenerateScalars.module k hA hM
  Module.End k M

/-- The composition ring on precisely these linear endomorphisms. -/
@[instance_reducible] def endRing : Ring (End k hA hM) :=
  letI := NondegenerateScalars.module k hA hM
  inferInstance

/-- The pointwise scalar module on precisely these linear endomorphisms. -/
@[instance_reducible] def endModule :
    letI := endRing k hA hM
    Module k (End k hA hM) :=
  letI := NondegenerateScalars.module k hA hM
  inferInstance

/-- Intrinsic scalar linearity of the actual completed action. -/
theorem act_smul (x : IdempotentedRingRightLimit A) (c : k) (m : M) :
    letI := NondegenerateScalars.module k hA hM
    IdempotentedRingRightLimitAction.act hM x (c • m) =
      c • IdempotentedRingRightLimitAction.act hM x m := by
  let := NondegenerateScalars.module k hA hM
  obtain ⟨e, he⟩ := hM m
  have hec : (e : A) • (c • m) = c • m := by
    rw [NondegenerateScalars.action_smul k hA hM,
      ← NondegenerateScalars.smul_action k hA hM, he]
  rw [IdempotentedRingRightLimitAction.act_eq hA hM x (c • m) e hec,
    IdempotentedRingRightLimitAction.act_eq hA hM x m e he,
    NondegenerateScalars.action_smul k hA hM,
    NondegenerateScalars.smul_action k hA hM]

/-- The actual extended action as a linear endomorphism for canonical scalars. -/
def linearEnd (x : IdempotentedRingRightLimit A) : End k hA hM :=
  letI := NondegenerateScalars.module k hA hM
  { IdempotentedRingRightLimit.actionAddHom hA hM x with map_smul' := act_smul k hA hM x }

@[simp] theorem linearEnd_coe (x : IdempotentedRingRightLimit A) :
    ⇑(linearEnd k hA hM x) = IdempotentedRingRightLimitAction.act hM x := rfl

/-- Equality of the entire curried action functions. -/
theorem linearEnd_function :
    (fun x => ⇑(linearEnd k hA hM x)) = IdempotentedRingRightLimitAction.act hM := rfl

@[simp] theorem linearEnd_toAddMonoidHom (x : IdempotentedRingRightLimit A) :
    (linearEnd k hA hM x).toAddMonoidHom = IdempotentedRingRightLimit.actionAddHom hA hM x := rfl

@[simp] theorem linearEnd_apply (x : IdempotentedRingRightLimit A) (m : M) :
    linearEnd k hA hM x m = IdempotentedRingRightLimitAction.act hM x m := rfl

/-- Every actual fixing idempotent computes the linear endomorphism. -/
theorem linearEnd_apply_eq (x : IdempotentedRingRightLimit A) (m : M)
    (e : Idempotent A) (he : (e : A) • m = m) :
    linearEnd k hA hM x m = x.val e • m :=
  IdempotentedRingRightLimitAction.act_eq hA hM x m e he

/-- The completed unital ring action on the named actual endomorphism ring. -/
def completedHom :
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    IdempotentedRingRightLimit A →+* End k hA hM := by
  letI := IdempotentedRingRightLimit.ring hA
  letI := endRing k hA hM
  letI := NondegenerateScalars.module k hA hM
  exact
    { toFun := linearEnd k hA hM
      map_zero' := LinearMap.ext (IdempotentedRingRightLimitAction.zero_act hA hM)
      map_one' := LinearMap.ext (IdempotentedRingRightLimitAction.unit_act hA hM)
      map_add' := fun x y => LinearMap.ext
        (IdempotentedRingRightLimitAction.add_act hA hM x y)
      map_mul' := fun x y => LinearMap.ext
        (IdempotentedRingRightLimitAction.product_act hA hM x y) }

@[simp] theorem completedHom_coe :
    ⇑(completedHom k hA hM) = linearEnd k hA hM := rfl

theorem completedHom_function :
    (fun x => ⇑(completedHom k hA hM x)) = IdempotentedRingRightLimitAction.act hM := rfl

theorem completedHom_additive_function :
    (fun x => (completedHom k hA hM x).toAddMonoidHom) =
      IdempotentedRingRightLimit.actionAddHom hA hM := rfl

@[simp] theorem completedHom_apply (x : IdempotentedRingRightLimit A) (m : M) :
    completedHom k hA hM x m = IdempotentedRingRightLimitAction.act hM x m := rfl

/-- Every actual fixing idempotent computes the bundled completed map. -/
theorem completedHom_apply_eq (x : IdempotentedRingRightLimit A) (m : M)
    (e : Idempotent A) (he : (e : A) • m = m) :
    completedHom k hA hM x m = x.val e • m :=
  linearEnd_apply_eq k hA hM x m e he

/-- The completed ring's multiplication composes, right factor first. -/
theorem completedHom_mul_apply (x y : IdempotentedRingRightLimit A) (m : M) :
    letI := IdempotentedRingRightLimit.ring hA
    completedHom k hA hM (x * y) m = completedHom k hA hM x (completedHom k hA hM y m) :=
  IdempotentedRingRightLimitAction.product_act hA hM x y m

@[simp] theorem completedHom_canonical (a : A) :
    completedHom k hA hM (IdempotentedRingRightLimit.canonicalRingHom hA a) =
      NondegenerateScalars.toLinearEndHom k hA hM a := by
  let := NondegenerateScalars.module k hA hM
  apply LinearMap.ext
  exact IdempotentedRingRightLimitAction.canonical_act hA hM a

/-- Compatibility is equality of entire bundled nonunital ring homomorphisms. -/
theorem completedHom_comp_canonical :
    letI := IdempotentedRingRightLimit.ring hA
    letI := endRing k hA hM
    (completedHom k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (NondegenerateScalars.toLinearEndHom k hA hM : A →ₙ+* End k hA hM) := by
  apply NonUnitalRingHom.ext
  exact completedHom_canonical k hA hM

theorem completedHom_canonical_function :
    (completedHom k hA hM) ∘ (IdempotentedRingRightLimit.canonicalRingHom hA) =
      ⇑(NondegenerateScalars.toLinearEndHom k hA hM) :=
  funext (completedHom_canonical k hA hM)

@[simp] theorem completedHom_canonical_apply (a : A) (m : M) :
    completedHom k hA hM (IdempotentedRingRightLimit.canonicalRingHom hA a) m = a • m :=
  IdempotentedRingRightLimitAction.canonical_act hA hM a m

/-- The canonical restriction retains the whole original additive action. -/
theorem completedHom_canonical_additive_function :
    (fun a => (completedHom k hA hM
        (IdempotentedRingRightLimit.canonicalRingHom hA a)).toAddMonoidHom) =
      fun a => NonUnitalModule.toEndHom (inferInstance : NonUnitalModule A M) a := by
  funext a
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.canonical_act hA hM a

end Individual

section Family

variable (k : Type uK) {A : Type uA} {I : Type uI} {M : I → Type uM}
  [CommSemiring k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]
  [∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)]
  (hA : IsIdempotented A) (hM : ∀ i, IsNondegenerate A (M i))

/-- The actual dependent product, with no replacement or transported carriers. -/
abbrev EndProduct : Type (max uI uM) := ∀ i, End k hA (hM i)

/-- Pointwise ring with coordinate multiplication given by composition. -/
@[instance_reducible] def productRing : Ring (EndProduct k hA hM) :=
  letI := fun i => endRing k hA (hM i)
  Pi.ring

/-- Pointwise scalars on the actual dependent product. -/
@[instance_reducible] def productModule :
    letI := productRing k hA hM
    Module k (EndProduct k hA hM) :=
  letI := fun i => endRing k hA (hM i)
  letI := fun i => endModule k hA (hM i)
  Pi.module I (fun i => End k hA (hM i)) k

/-- The simultaneous original nonunital algebra action. -/
def original :
    letI := productRing k hA hM
    letI := productModule k hA hM
    A →ₙₐ[k] EndProduct k hA hM := by
  letI := productRing k hA hM
  letI := productModule k hA hM
  letI := fun i => NondegenerateScalars.module k hA (hM i)
  exact
    { toFun := fun a i => NondegenerateScalars.toLinearEndHom k hA (hM i) a
      map_zero' := funext fun i => map_zero (NondegenerateScalars.toLinearEndHom k hA (hM i))
      map_add' := fun a b => funext fun i =>
        map_add (NondegenerateScalars.toLinearEndHom k hA (hM i)) a b
      map_mul' := fun a b => funext fun i =>
        map_mul (NondegenerateScalars.toLinearEndHom k hA (hM i)) a b
      map_smul' := fun c a => funext fun i =>
        map_smul (NondegenerateScalars.toLinearEndHom k hA (hM i)) c a }

/-- The simultaneous actual completed unital ring action. -/
def completed :
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    IdempotentedRingRightLimit A →+* EndProduct k hA hM := by
  letI := IdempotentedRingRightLimit.ring hA
  letI := productRing k hA hM
  exact
    { toFun := fun x i => completedHom k hA (hM i) x
      map_zero' := funext fun i => map_zero (completedHom k hA (hM i))
      map_one' := funext fun i => map_one (completedHom k hA (hM i))
      map_add' := fun x y => funext fun i => map_add (completedHom k hA (hM i)) x y
      map_mul' := fun x y => funext fun i => map_mul (completedHom k hA (hM i)) x y }

/-- The actual coordinate projection, retaining its unit law. -/
def projection (i : I) :
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    EndProduct k hA hM →+* End k hA (hM i) :=
  letI := productRing k hA hM
  letI := endRing k hA (hM i)
  { toFun := fun f => f i
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }

/-- The same coordinate projection as a nonunital algebra homomorphism. -/
def algebraProjection (i : I) :
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    EndProduct k hA hM →ₙₐ[k] End k hA (hM i) :=
  letI := productRing k hA hM
  letI := productModule k hA hM
  letI := endRing k hA (hM i)
  letI := endModule k hA (hM i)
  { (projection k hA hM i).toNonUnitalRingHom with map_smul' := fun _ _ => rfl }

@[simp] theorem original_coe :
    ⇑(original k hA hM) =
      fun a i => NondegenerateScalars.toLinearEndHom k hA (hM i) a := rfl

theorem original_coordinate (i : I) :
    (fun a => original k hA hM a i) = ⇑(NondegenerateScalars.toLinearEndHom k hA (hM i)) := rfl

theorem original_function :
    (fun a i => ⇑(original k hA hM a i)) = fun a _ m => a • m := rfl

theorem original_additive_function :
    (fun a i => (original k hA hM a i).toAddMonoidHom) =
      fun a i => NonUnitalModule.toEndHom (inferInstance : NonUnitalModule A (M i)) a := rfl

@[simp] theorem original_apply (a : A) (i : I) (m : M i) :
    original k hA hM a i m = a • m := rfl

@[simp] theorem completed_coe :
    ⇑(completed k hA hM) = fun x i => completedHom k hA (hM i) x := rfl

theorem completed_coordinate (i : I) :
    (fun x => completed k hA hM x i) = ⇑(completedHom k hA (hM i)) := rfl

theorem completed_function :
    (fun x i => ⇑(completed k hA hM x i)) =
      fun x i => IdempotentedRingRightLimitAction.act (hM i) x := rfl

theorem completed_additive_function :
    (fun x i => (completed k hA hM x i).toAddMonoidHom) =
      fun x i => IdempotentedRingRightLimit.actionAddHom hA (hM i) x := rfl

@[simp] theorem completed_apply (x : IdempotentedRingRightLimit A) (i : I) (m : M i) :
    completed k hA hM x i m = IdempotentedRingRightLimitAction.act (hM i) x m := rfl

theorem completed_apply_eq (x : IdempotentedRingRightLimit A) (i : I) (m : M i)
    (e : Idempotent A) (he : (e : A) • m = m) :
    completed k hA hM x i m = x.val e • m :=
  linearEnd_apply_eq k hA (hM i) x m e he

@[simp] theorem projection_coe (i : I) :
    ⇑(projection k hA hM i) = fun f => f i := rfl

@[simp] theorem projection_apply (i : I) (f : EndProduct k hA hM) (m : M i) :
    projection k hA hM i f m = f i m := rfl

@[simp] theorem algebraProjection_coe (i : I) :
    ⇑(algebraProjection k hA hM i) = fun f => f i := rfl

@[simp] theorem algebraProjection_apply (i : I) (f : EndProduct k hA hM) (m : M i) :
    algebraProjection k hA hM i f m = f i m := rfl

@[simp] theorem algebraProjection_toNonUnitalRingHom (i : I) :
    (algebraProjection k hA hM i : EndProduct k hA hM →ₙ+* End k hA (hM i)) =
      (projection k hA hM i).toNonUnitalRingHom := rfl

@[simp] theorem projection_original (i : I) :
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    letI := endModule k hA (hM i)
    (algebraProjection k hA hM i).comp (original k hA hM) =
      NondegenerateScalars.toLinearEndHom k hA (hM i) := rfl

@[simp] theorem projection_original_ring (i : I) :
    letI := productRing k hA hM
    letI := productModule k hA hM
    letI := endRing k hA (hM i)
    (projection k hA hM i).toNonUnitalRingHom.comp
        (original k hA hM : A →ₙ+* EndProduct k hA hM) =
      (NondegenerateScalars.toLinearEndHom k hA (hM i) : A →ₙ+* End k hA (hM i)) := rfl

@[simp] theorem projection_completed (i : I) :
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := endRing k hA (hM i)
    (projection k hA hM i).comp (completed k hA hM) = completedHom k hA (hM i) := rfl

/-- The entire completed map extends the original after forgetting scalar preservation. -/
theorem completed_comp_canonical :
    letI := IdempotentedRingRightLimit.ring hA
    letI := productRing k hA hM
    letI := productModule k hA hM
    (completed k hA hM).toNonUnitalRingHom.comp
        (IdempotentedRingRightLimit.canonicalRingHom hA) =
      (original k hA hM : A →ₙ+* EndProduct k hA hM) := by
  apply NonUnitalRingHom.ext
  intro a
  funext i
  exact completedHom_canonical k hA (hM i) a

theorem completed_canonical_function :
    (completed k hA hM) ∘ (IdempotentedRingRightLimit.canonicalRingHom hA) =
      ⇑(original k hA hM) := by
  funext a i
  exact completedHom_canonical k hA (hM i) a

@[simp] theorem completed_canonical_apply (a : A) (i : I) (m : M i) :
    completed k hA hM (IdempotentedRingRightLimit.canonicalRingHom hA a) i m = a • m :=
  completedHom_canonical_apply k hA (hM i) a m

/-- Product multiplication composes the actual endomorphisms, right factor first. -/
theorem product_mul_apply (f g : EndProduct k hA hM) (i : I) (m : M i) :
    letI := productRing k hA hM
    (f * g) i m = f i (g i m) := rfl

/-- Original product actions have the same composition order. -/
theorem original_mul_apply (a b : A) (i : I) (m : M i) :
    original k hA hM (a * b) i m = original k hA hM a i (original k hA hM b i m) :=
  mul_smul a b m

/-- Completed product actions have the same composition order. -/
theorem completed_mul_apply (x y : IdempotentedRingRightLimit A) (i : I) (m : M i) :
    letI := IdempotentedRingRightLimit.ring hA
    completed k hA hM (x * y) i m = completed k hA hM x i (completed k hA hM y i m) :=
  IdempotentedRingRightLimitAction.product_act hA (hM i) x y m

end Family

section Complex

variable {A : Type uA} {I : Type uI} {M : I → Type uM}
  [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)]
  (hA : IsIdempotented A) (hM : ∀ i, IsNondegenerate A (M i))

/-- The exact complex simultaneous original action on the original carriers. -/
abbrev complexOriginal := original ℂ hA hM

/-- The exact complex simultaneous completed action on the original carriers. -/
abbrev complexCompleted := completed ℂ hA hM

@[simp] theorem complexOriginal_apply (a : A) (i : I) (m : M i) :
    complexOriginal hA hM a i m = a • m := rfl

@[simp] theorem complexCompleted_apply (x : IdempotentedRingRightLimit A) (i : I) (m : M i) :
    complexCompleted hA hM x i m = IdempotentedRingRightLimitAction.act (hM i) x m := rfl

end Complex

end Langlands.Algebra.NondegenerateModuleLinearActions
