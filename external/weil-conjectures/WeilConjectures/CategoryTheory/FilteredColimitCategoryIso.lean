/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.FinCategory.Basic

@[expose] public section

universe z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph and its
finite-diagram remark.
(blueprint: lem-weil-pbc-filtered-colimit-category-iso).

Proof: Encode an invertible arrow as the image of the unique arrow from false to
true in the finite groupoid on two objects with one arrow between any ordered
pair. The functor is defined from the given isomorphism by choosing an isomorphism
from each of its endpoints to the source. Lift this finite functor to a stage.
The lifted arrow is invertible because its inverse in the two-object groupoid is
preserved by the stage functor. Equality of the composite functor with the given
one yields equality of its image as an Arrow, including both endpoints. Conversely,
a stage isomorphism maps to an isomorphism under any functor. No compatibility or
colimit hypothesis is required for this consequence of finite-functor lifting. -/
theorem filteredColimit_category_iso_clause
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∀ (_s : Category.{z} O), ∀ (V : ∀ j : J, F.obj j ⥤ O),
    (∀ (D : Type z) [SmallCategory D] [FinCategory D] (d : D ⥤ O),
      ∃ (j : J) (dj : D ⥤ F.obj j), dj ⋙ V j = d) →
    (∀ a : Arrow O, IsIso a.hom ↔
      ∃ (j : J) (b : Arrow (F.obj j)),
        IsIso b.hom ∧ (V j).mapArrow.obj b = a) := by
  classical
  intro O s V hLift a
  constructor
  · intro ha
    let := ha
    let D := ULift.{z} Bool
    let : SmallCategory D :=
      { Hom := fun _ _ ↦ PUnit
        id := fun _ ↦ PUnit.unit
        comp := fun _ _ ↦ PUnit.unit }
    let : Fintype D := ULift.fintype _
    let : FinCategory D :=
      { fintypeObj := inferInstance
        fintypeHom := fun _ _ ↦ (show Fintype PUnit from inferInstance) }
    let X : D → O := fun i ↦ if i.down then a.right else a.left
    let e : ∀ i : D, X i ≅ a.left := fun i ↦ by
      cases i with
      | up i => cases i
                · exact Iso.refl _
                · exact (asIso a.hom).symm
    let d : D ⥤ O :=
      { obj := X
        map := fun {i j} _ ↦ (e i).hom ≫ (e j).inv
        map_id := fun i ↦ by simp
        map_comp := fun _ _ ↦ by simp }
    obtain ⟨j, dj, hdj⟩ := hLift D d
    let i₀ : D := ⟨false⟩
    let i₁ : D := ⟨true⟩
    let f : i₀ ⟶ i₁ := PUnit.unit
    let g : i₁ ⟶ i₀ := PUnit.unit
    have hfg : f ≫ g = 𝟙 i₀ := rfl
    have hgf : g ≫ f = 𝟙 i₁ := rfl
    let : IsIso f := ⟨⟨g, hfg, hgf⟩⟩
    refine ⟨j, Arrow.mk (dj.map f), ?_, ?_⟩
    · change IsIso (dj.map f)
      infer_instance
    · have h := congrArg (fun H : D ⥤ O ↦ H.mapArrow.obj (Arrow.mk f)) hdj
      change Arrow.mk ((V j).map (dj.map f)) = a
      change Arrow.mk ((V j).map (dj.map f)) = Arrow.mk (d.map f) at h
      simpa [d, e, f, i₀, i₁, X] using h
  · rintro ⟨j, b, hb, hba⟩
    let := hb
    rw [← hba]
    change IsIso ((V j).map b.hom)
    infer_instance

end CategoryTheory
