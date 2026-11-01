import Langlands.Algebra.NonUnitalModuleProducts
import Langlands.Algebra.NondegenerateModuleAdjunction

/-!
# Actual products of nondegenerate original modules

Renard I.6: take the nondegenerate part of the coordinatewise ambient product.
The index and coefficient universes are independent; the category's carrier
universe is explicitly large enough to contain the index type.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateModuleProducts

open CategoryTheory CategoryTheory.Limits

universe uA uI uM

variable {A : Type uA} [NonUnitalRing A] {I : Type uI}
  (P : I → NondegenerateModuleCat.{uA, max uI uM} A)

/-- The actual coordinatewise ambient product, before taking its part. -/
abbrev ambient : NonUnitalModuleCat.{uA, max uI uM} A :=
  NonUnitalModuleCat.of A (∀ i, (P i).obj)

/-- The product object is the actual nondegenerate part of that function module. -/
def object (hA : IsIdempotented A) : NondegenerateModuleCat.{uA, max uI uM} A :=
  (nondegeneratePartFunctor hA).obj (ambient P)

/-- A tuple belongs to the product exactly when a single idempotent fixes it. -/
theorem mem_part_iff (hA : IsIdempotented A) (x : ambient P) :
    x ∈ nondegeneratePart hA (ambient P) ↔
      ∃ e : Idempotent A, ∀ i, (e : A) • x i = x i := by
  change (∃ e : Idempotent A, (e : A) • x = x) ↔ _
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun i => congrFun he i⟩
  · rintro ⟨e, he⟩
    exact ⟨e, funext he⟩

/-- The original coordinate projection, restricted to the actual part. -/
def projection (hA : IsIdempotented A) (i : I) : object P hA ⟶ P i :=
  ObjectProperty.homMk
    { toFun := fun x => x.val i
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Assemble original maps as a tuple, then factor into its actual part. -/
def lift (hA : IsIdempotented A)
    {N : NondegenerateModuleCat.{uA, max uI uM} A} (f : ∀ i, N ⟶ P i) :
    N ⟶ object P hA :=
  ObjectProperty.homMk
    (NonUnitalModuleHom.factorNondegeneratePart hA N.property
      { toFun := fun n i => (f i).hom.toAddMonoidHom n
        map_zero' := funext fun i => (f i).hom.map_zero
        map_add' := fun n n' => funext fun i => (f i).hom.map_add n n'
        map_smul' := fun a n => funext fun i => (f i).hom.map_smul a n })

@[simp] theorem projection_apply (hA : IsIdempotented A) (i : I)
    (x : (object P hA).obj) :
    (projection P hA i).hom.toAddMonoidHom x = x.val i := rfl

@[simp] theorem lift_apply (hA : IsIdempotented A)
    {N : NondegenerateModuleCat.{uA, max uI uM} A}
    (f : ∀ i, N ⟶ P i) (n : N.obj) (i : I) :
    ((lift P hA f).hom.toAddMonoidHom n).val i =
      (f i).hom.toAddMonoidHom n := rfl

@[simp] theorem lift_projection (hA : IsIdempotented A)
    {N : NondegenerateModuleCat.{uA, max uI uM} A}
    (f : ∀ i, N ⟶ P i) (i : I) :
    lift P hA f ≫ projection P hA i = f i := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro n
  rfl

/-- Original maps into the actual part are determined by their coordinates. -/
theorem hom_ext (hA : IsIdempotented A)
    {N : NondegenerateModuleCat.{uA, max uI uM} A}
    {f g : N ⟶ object P hA}
    (h : ∀ i, f ≫ projection P hA i = g ≫ projection P hA i) : f = g := by
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro n
  apply Subtype.ext
  funext i
  exact congrArg (fun k : N ⟶ P i => k.hom.toAddMonoidHom n) (h i)

@[simp] theorem lift_eta (hA : IsIdempotented A)
    {N : NondegenerateModuleCat.{uA, max uI uM} A}
    (f : N ⟶ object P hA) :
    lift P hA (fun i => f ≫ projection P hA i) = f := by
  apply hom_ext P hA
  intro i
  exact lift_projection P hA _ i

/-- The cone retains the actual coordinate projections of original modules. -/
def fan (hA : IsIdempotented A) : Fan P :=
  Fan.mk (object P hA) (projection P hA)

/-- The original lift and coordinate extensionality prove the product property. -/
def fanIsLimit (hA : IsIdempotented A) : IsLimit (fan P hA) :=
  Fan.IsLimit.mk _ (fun s => lift P hA s.proj)
    (fun s i => lift_projection P hA s.proj i)
    (fun s _m hm => hom_ext P hA (fun i => (hm i).trans
      (lift_projection P hA s.proj i).symm))

/-- Product existence is supplied by this concrete cone. -/
theorem hasProduct (hA : IsIdempotented A) : HasProduct P :=
  ⟨⟨fan P hA, fanIsLimit P hA⟩⟩

/-! Complete unapplied interfaces expose the independent universes and index bound. -/

example : {A : Type uA} → [NonUnitalRing A] → {I : Type uI} →
    (P : I → NondegenerateModuleCat.{uA, max uI uM} A) →
    (hA : IsIdempotented A) → IsLimit (fan P hA) :=
  @fanIsLimit.{uA, uI, uM}

example : {A : Type uA} → [NonUnitalRing A] → {I : Type uI} →
    (P : I → NondegenerateModuleCat.{uA, max uI uM} A) →
    (hA : IsIdempotented A) → HasProduct P :=
  @hasProduct.{uA, uI, uM}

example : {A : Type} → [NonUnitalRing A] → {I : Type 1} →
    (P : I → NondegenerateModuleCat.{0, 1} A) →
    (hA : IsIdempotented A) → IsLimit (fan.{0, 1, 0} P hA) :=
  @fanIsLimit.{0, 1, 0}

example : {A : Type 1} → [NonUnitalRing A] → {I : Type} →
    (P : I → NondegenerateModuleCat.{1, 0} A) →
    (hA : IsIdempotented A) → IsLimit (fan.{1, 0, 0} P hA) :=
  @fanIsLimit.{1, 0, 0}

end Langlands.Algebra.NondegenerateModuleProducts
