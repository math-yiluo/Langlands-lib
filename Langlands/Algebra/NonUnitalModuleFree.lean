import Langlands.Algebra.NonUnitalModuleDirectSum
import Langlands.Algebra.RegularModuleHom
import Langlands.Algebra.NondegenerateModuleNaturalEndEvaluation

/-!
# Actual free modules over an idempotented nonunital ring

Renard I.5.3, printed p.27 / PDF p.33. Freeness means a direct sum of
copies of the original regular module, without a projectivity assertion.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra.NonUnitalModuleFree

universe uA uL uI uM

local instance (I : Type uI) : DecidableEq I := Classical.decEq I

variable {A : Type uA} [NonUnitalRing A]

/-- The original regular carrier, with an explicit universe lift. -/
abbrev Regular (A : Type uA) := ULift.{uL} A

/-- Original multiplication on each lifted copy of A. -/
instance regularAction : NonUnitalModule A (Regular.{uA, uL} A) :=
  NondegenerateModuleNaturalEndEvaluation.liftedAction.{uA, uL} A

@[simp] theorem regular_smul_down (a : A) (x : Regular.{uA, uL} A) :
    (a • x).down = a * x.down := rfl

section OriginalRegular

local instance : NonUnitalModule A A := NonUnitalModule.regular A

/-- The actual additive intertwiner removing only the universe lift. -/
def regularDown : NonUnitalModuleHom A (Regular.{uA, uL} A) A where
  toFun := ULift.down
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse original intertwiner inserts only the universe lift. -/
def regularUp : NonUnitalModuleHom A A (Regular.{uA, uL} A) where
  toFun := ULift.up
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem regularDown_comp_up :
    (regularDown.{uA, uL} (A := A)).comp regularUp = NonUnitalModuleHom.id A A := rfl

theorem regularUp_comp_down :
    (regularUp.{uA, uL} (A := A)).comp regularDown =
      NonUnitalModuleHom.id A (Regular.{uA, uL} A) := rfl

end OriginalRegular

/-- A local unit for the actual coefficient fixes its lifted regular vector. -/
theorem regular_isNondegenerate (hA : IsIdempotented A) :
    IsNondegenerate A (Regular.{uA, uL} A) := by
  intro x
  obtain ⟨e, he⟩ := hA.exists_mem_corner x.down
  exact ⟨e, congrArg ULift.up ((Idempotent.mem_corner_iff e x.down).mp he).1⟩

/-- A copy of the original regular module in the chosen carrier universe. -/
def regularObject (hA : IsIdempotented A) :
    NondegenerateModuleCat.{uA, max uA uL} A :=
  NondegenerateModuleNaturalEndEvaluation.liftedRegularObject.{uA, uL} hA

/-- The actual finite-support sum of copies of the original regular module. -/
abbrev Carrier (A : Type uA) [NonUnitalRing A] (I : Type uI) :=
  @DFinsupp I (fun _ => Regular.{uA, uL} A) (fun _ => inferInstance)

instance carrierAddCommGroup (I : Type uI) :
    AddCommGroup (Carrier.{uA, uL, uI} A I) := by
  letI : ∀ _ : I, AddCommGroup (Regular.{uA, uL} A) := fun _ => inferInstance
  exact inferInstance

/-- The actual coordinatewise sum action on the regular copies. -/
instance carrierAction (I : Type uI) :
    NonUnitalModule A (Carrier.{uA, uL, uI} A I) := by
  letI : ∀ _ : I, AddCommGroup (Regular.{uA, uL} A) := fun _ => inferInstance
  letI : ∀ _ : I, NonUnitalModule A (Regular.{uA, uL} A) := fun _ => regularAction
  exact NonUnitalModuleDirectSum.action (A := A) (fun _ : I => Regular.{uA, uL} A)

@[simp] theorem smul_apply (I : Type uI) (a : A)
    (x : Carrier.{uA, uL, uI} A I) (i : I) : (a • x) i = a • x i := rfl

/-- The source's displayed free module, with its original coordinatewise action. -/
def object (hA : IsIdempotented A) (I : Type uI) :
    NondegenerateModuleCat.{uA, max uI (max uA uL)} A := by
  letI : ∀ _ : I, AddCommGroup (Regular.{uA, uL} A) := fun _ => inferInstance
  letI : ∀ _ : I, NonUnitalModule A (Regular.{uA, uL} A) := fun _ => regularAction
  exact ⟨NonUnitalModuleCat.of A (Carrier.{uA, uL, uI} A I),
    NonUnitalModuleDirectSum.isNondegenerate
      (fun _ : I => Regular.{uA, uL} A) hA (fun _ => regular_isNondegenerate hA)⟩

theorem object_carrier (hA : IsIdempotented A) (I : Type uI) :
    (object.{uA, uL, uI} hA I).obj.carrier = Carrier.{uA, uL, uI} A I := rfl

theorem object_action (hA : IsIdempotented A) (I : Type uI) :
    (object.{uA, uL, uI} hA I).obj.isModule = carrierAction I := rfl

/-- The actual singleton map into the displayed free carrier. -/
def inclusion (I : Type uI) (i : I) :
    NonUnitalModuleHom A (Regular.{uA, uL} A) (Carrier.{uA, uL, uI} A I) := by
  letI : ∀ _ : I, AddCommGroup (Regular.{uA, uL} A) := fun _ => inferInstance
  letI : ∀ _ : I, NonUnitalModule A (Regular.{uA, uL} A) := fun _ => regularAction
  exact NonUnitalModuleDirectSum.inclusion (A := A) (fun _ : I => Regular.{uA, uL} A) i

@[simp] theorem inclusion_apply (I : Type uI) (i : I) (a : Regular.{uA, uL} A) :
    inclusion I i a = DFinsupp.single i a := rfl

variable {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

/-- An original vector gives the original regular-source orbit map a ↦ a m. -/
def orbit (m : M) : NonUnitalModuleHom A (Regular.{uA, uL} A) M where
  toFun x := x.down • m
  map_zero' := NonUnitalModule.zero_smul m
  map_add' x y := NonUnitalModule.add_smul x.down y.down m
  map_smul' a x := mul_smul a x.down m

@[simp] theorem orbit_apply (m : M) (a : A) :
    orbit.{uA, uL, uM} m (ULift.up a) = a • m := rfl

/-- Descend the actual orbit maps of a chosen family of original vectors. -/
def fromFamily {I : Type uI} (v : I → M) :
    NonUnitalModuleHom A (Carrier.{uA, uL, uI} A I) M := by
  letI : ∀ _ : I, AddCommGroup (Regular.{uA, uL} A) := fun _ => inferInstance
  letI : ∀ _ : I, NonUnitalModule A (Regular.{uA, uL} A) := fun _ => regularAction
  exact NonUnitalModuleDirectSum.desc (fun _ : I => Regular.{uA, uL} A)
    (fun i => orbit (v i))

@[simp] theorem fromFamily_single {I : Type uI} (v : I → M) (i : I) (a : A) :
    fromFamily.{uA, uL, uI, uM} v
        (inclusion I i (ULift.up a)) = a • v i := by
  let : ∀ _ : I, AddCommGroup (Regular.{uA, uL} A) := fun _ => inferInstance
  let : ∀ _ : I, NonUnitalModule A (Regular.{uA, uL} A) := fun _ => regularAction
  exact NonUnitalModuleDirectSum.desc_inclusion
    (fun _ : I => Regular.{uA, uL} A) (fun j => orbit (v j)) i (ULift.up a)

/-- Freeness means an isomorphism to an actual sum of regular copies. -/
def IsFree (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) : Prop :=
  ∃ I : Type (max uA uM), Nonempty (M ≅ object.{uA, uM, max uA uM} hA I)

theorem object_isFree (hA : IsIdempotented A) (I : Type (max uA uM)) :
    IsFree.{uA, uM} hA (object.{uA, uM, max uA uM} hA I) :=
  ⟨I, ⟨Iso.refl _⟩⟩

/-! Entire interfaces retain independent coefficient, index, lift and test universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {I : Type uI} → (I → M) →
      NonUnitalModuleHom A (Carrier.{uA, uL, uI} A I) M :=
  @fromFamily.{uA, uL, uI, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    NondegenerateModuleCat.{uA, max uA uM} A → Prop :=
  @IsFree.{uA, uM}

end Langlands.Algebra.NonUnitalModuleFree
