import Langlands.CategoryTheory.RenardFiniteType
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Renard's local finite-type condition and source AB6

Source: Renard (9 July 2026), A.VI.3, printed page 263 / PDF269.
The sized comparison uses an independent family universe. The canonical
condition uses all finite-type subobjects in the actual subobject type.
-/

universe w v u

open CategoryTheory

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C]

/-- The finite-type subobjects of `X` have top as their least upper bound
in the existing categorical subobject order. -/
def IsLocallyFiniteTypeObject (X : C) : Prop :=
  IsLUB {P : Subobject X | IsFiniteTypeObject (P : C)} (⊤ : Subobject X)

/-- Every object is a sum of its finite-type subobjects. -/
def IsLocallyFiniteTypeCategory (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, IsLocallyFiniteTypeObject X

/-- Renard's AB6, in the source abelian context: local finite type.
The separate source Grothendieck hypothesis is not part of this predicate. -/
abbrev SourceAB6 (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsLocallyFiniteTypeCategory C

/-- There is a `w`-indexed covering family of finite-type subobjects.
The family may be empty. -/
@[pp_with_univ]
def IsLocallyFiniteTypeObjectOfSize (X : C) : Prop :=
  ∃ (I : Type w) (F : I → Subobject X),
    (∀ i : I, IsFiniteTypeObject (F i : C)) ∧
      IsLUB (Set.range F) (⊤ : Subobject X)

/-- Every object admits a `w`-indexed covering family of finite-type
subobjects. -/
@[pp_with_univ]
def IsLocallyFiniteTypeCategoryOfSize (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, IsLocallyFiniteTypeObjectOfSize.{w} X

/-- Any sized finite-type cover implies the canonical local finite-type
condition, with no smallness assumption. -/
theorem IsLocallyFiniteTypeObjectOfSize.isLocallyFiniteTypeObject {X : C}
    (h : IsLocallyFiniteTypeObjectOfSize.{w} X) :
    IsLocallyFiniteTypeObject X := by
  obtain ⟨I, F, hfinite, hcover⟩ := h
  refine ⟨?_, ?_⟩
  · intro P _
    exact le_top
  · intro Q hQ
    apply hcover.2
    rintro P ⟨i, rfl⟩
    exact hQ (hfinite i)

/-- The full subtype of finite-type subobjects gives a cover indexed in
`Type (max u v)`. No shrinking of the actual subobject type is used. -/
theorem IsLocallyFiniteTypeObject.ofSize {X : C}
    (h : IsLocallyFiniteTypeObject X) :
    IsLocallyFiniteTypeObjectOfSize.{max u v} X := by
  let I := {P : Subobject X // IsFiniteTypeObject (P : C)}
  let F : I → Subobject X := fun P => P.val
  have hrange : Set.range F =
      {P : Subobject X | IsFiniteTypeObject (P : C)} := by
    ext P
    constructor
    · rintro ⟨Q, rfl⟩
      exact Q.property
    · intro hP
      exact ⟨⟨P, hP⟩, rfl⟩
  refine ⟨I, F, (fun P => P.property), ?_⟩
  simpa only [hrange, IsLocallyFiniteTypeObject] using h

/-- The canonical and sized object conditions agree at the universe of
the actual subobject type. -/
theorem isLocallyFiniteTypeObject_iff_ofSize {X : C} :
    IsLocallyFiniteTypeObject X ↔
      IsLocallyFiniteTypeObjectOfSize.{max u v} X :=
  ⟨IsLocallyFiniteTypeObject.ofSize,
    IsLocallyFiniteTypeObjectOfSize.isLocallyFiniteTypeObject⟩

/-- A sized category-wide condition at any family universe implies the
canonical category-wide condition. -/
theorem IsLocallyFiniteTypeCategoryOfSize.isLocallyFiniteTypeCategory
    (h : IsLocallyFiniteTypeCategoryOfSize.{w} C) :
    IsLocallyFiniteTypeCategory C :=
  fun X => (h X).isLocallyFiniteTypeObject

/-- The canonical and sized category conditions agree at the universe of
the actual subobject types. -/
theorem isLocallyFiniteTypeCategory_iff_ofSize :
    IsLocallyFiniteTypeCategory C ↔
      IsLocallyFiniteTypeCategoryOfSize.{max u v} C :=
  ⟨fun h X => (h X).ofSize,
    IsLocallyFiniteTypeCategoryOfSize.isLocallyFiniteTypeCategory⟩

end Langlands.Renard
