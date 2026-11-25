/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Conservative families of points at a larger universe

If a small family of points of a site is conservative, so is the family obtained by lifting
every member to a larger universe with
`CategoryTheory.GrothendieckTopology.Point.ulift`.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  [HasSheafify J (Type (max w w'))]
  {ι : Type*} [Small.{w} ι] (Φ : ι → GrothendieckTopology.Point.{w} J)

/-- If a small family of points of a site is conservative, so is the family of the
universe-lifted points. -/
lemma ulift (h : (ObjectProperty.ofObj Φ).IsConservativeFamilyOfPoints) :
    (ObjectProperty.ofObj (fun i ↦ (Φ i).ulift.{w'})).IsConservativeFamilyOfPoints := by
  have : LocallySmall.{max w w'} C := ⟨fun _ _ ↦ small_lift.{v, w', w} _⟩
  refine .mk' (fun X S hS ↦ ?_)
  obtain ⟨α, T, f, rfl⟩ := S.exists_eq_ofArrows
  rw [h.jointly_reflect_ofArrows_mem_of_small]
  rintro ⟨-, ⟨i⟩⟩ x
  obtain ⟨Y, -, ⟨Z, p, -, ⟨j⟩, rfl⟩, y, hy⟩ :=
    hS ⟨(Φ i).ulift.{w'}, ⟨i⟩⟩ (ULift.up x)
  refine ⟨j, (Φ i).fiber.map p y.down, ?_⟩
  simpa using congrArg ULift.down hy

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints
