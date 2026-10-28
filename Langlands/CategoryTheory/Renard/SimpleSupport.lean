import Langlands.CategoryTheory.Renard.CompositionChains
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Renard A.IX: objects supported on simple isomorphism classes

The full subcategory `M_S` on printed page 268 / PDF page 274 of Renard's
9 July 2026 French edition consists of the objects whose simple subquotient
classes all belong to `S`. We use the actual public simple subquotients.
The definitions also make sense for arbitrary sets of object classes in an
arbitrary abelian category. No closure, maximality or splitting result is assumed.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every simple subquotient class of `X` belongs to `S`. -/
def HasSimpleSupport (S : Set (ObjectClass C)) (X : C) : Prop :=
  simpleSubquotientClasses X ⊆ S

/-- The objects of Renard's supported full subcategory `M_S`. -/
def simpleSupportObjects (S : Set (ObjectClass C)) : ObjectProperty C :=
  fun X => HasSimpleSupport S X

/-- The actual full subcategory of objects supported on `S`. -/
abbrev SimpleSupportSubcategory (S : Set (ObjectClass C)) : Type u :=
  (simpleSupportObjects S).FullSubcategory

/-- The actual fully faithful inclusion of the supported full subcategory. -/
abbrev simpleSupportInclusion (S : Set (ObjectClass C)) :
    SimpleSupportSubcategory S ⥤ C :=
  (simpleSupportObjects S).ι

/-- The actual subobjects of `X` whose underlying objects are supported on `S`. -/
def simpleSupportSubobjects (S : Set (ObjectClass C)) (X : C) : Set (Subobject X) :=
  {P | HasSimpleSupport S (P : C)}

theorem hasSimpleSupport_iff_subset (S : Set (ObjectClass C)) (X : C) :
    HasSimpleSupport S X ↔ simpleSubquotientClasses X ⊆ S :=
  Iff.rfl

/-- The support condition quantified over every actual simple quotient `B / A`
of subobjects `A ≤ B` of `X`. -/
theorem hasSimpleSupport_iff (S : Set (ObjectClass C)) (X : C) :
    HasSimpleSupport S X ↔
      ∀ (A B : Subobject X) (h : A ≤ B),
        Simple (cokernel (Subobject.ofLE A B h)) →
          objectClass (cokernel (Subobject.ofLE A B h)) ∈ S := by
  constructor
  · intro h A B hAB hs
    exact h ⟨A, B, hAB, hs, rfl⟩
  · rintro h q ⟨A, B, hAB, hs, rfl⟩
    exact h A B hAB hs

theorem simpleSupportObjects_apply (S : Set (ObjectClass C)) (X : C) :
    simpleSupportObjects S X ↔ HasSimpleSupport S X :=
  Iff.rfl

theorem simpleSupportInclusion_obj (S : Set (ObjectClass C))
    (X : SimpleSupportSubcategory S) :
    (simpleSupportInclusion S).obj X = X.obj :=
  rfl

theorem hasSimpleSupport_inclusion_obj (S : Set (ObjectClass C))
    (X : SimpleSupportSubcategory S) :
    HasSimpleSupport S ((simpleSupportInclusion S).obj X) :=
  X.property

theorem mem_simpleSupportSubobjects_iff (S : Set (ObjectClass C)) (X : C)
    (P : Subobject X) :
    P ∈ simpleSupportSubobjects S X ↔ HasSimpleSupport S (P : C) :=
  Iff.rfl

theorem hasSimpleSupport_mono {S T : Set (ObjectClass C)} (hST : S ⊆ T)
    {X : C} (hX : HasSimpleSupport S X) : HasSimpleSupport T X :=
  fun _ hq => hST (hX hq)

theorem simpleSupportObjects_mono {S T : Set (ObjectClass C)} (hST : S ⊆ T) :
    simpleSupportObjects S ≤ simpleSupportObjects T :=
  fun _ hX => hasSimpleSupport_mono hST hX

theorem simpleSupportSubobjects_mono {S T : Set (ObjectClass C)} (hST : S ⊆ T)
    (X : C) : simpleSupportSubobjects S X ⊆ simpleSupportSubobjects T X :=
  fun _ hP => hasSimpleSupport_mono hST hP

theorem hasSimpleSupport_inter_iff (S T : Set (ObjectClass C)) (X : C) :
    HasSimpleSupport (S ∩ T) X ↔ HasSimpleSupport S X ∧ HasSimpleSupport T X := by
  constructor
  · intro h
    exact ⟨fun _ hq => (h hq).1, fun _ hq => (h hq).2⟩
  · rintro ⟨hS, hT⟩ q hq
    exact ⟨hS hq, hT hq⟩

theorem simpleSupportSubobjects_inter (S T : Set (ObjectClass C)) (X : C) :
    simpleSupportSubobjects (S ∩ T) X =
      simpleSupportSubobjects S X ∩ simpleSupportSubobjects T X := by
  ext P
  exact hasSimpleSupport_inter_iff S T (P : C)

/-- Every simple subquotient class is a simple class, with no finite-length
assumption on `X`. -/
theorem hasSimpleSupport_simpleClasses (X : C) :
    HasSimpleSupport (simpleClasses C) X :=
  simpleSubquotientClasses_subset_simpleClasses X

/-- Classes outside `simpleClasses C` do not affect the support condition. -/
theorem hasSimpleSupport_inter_simpleClasses_iff (S : Set (ObjectClass C)) (X : C) :
    HasSimpleSupport (S ∩ simpleClasses C) X ↔ HasSimpleSupport S X := by
  constructor
  · intro h
    exact ((hasSimpleSupport_inter_iff S (simpleClasses C) X).mp h).1
  · intro h
    exact (hasSimpleSupport_inter_iff S (simpleClasses C) X).mpr
      ⟨h, hasSimpleSupport_simpleClasses X⟩

end

end Langlands.Renard
