/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Torsors with a specified section

Source: Stacks Project, Cohomology on Sites, Tag 03AJ, and its relative refinement
(blueprint: def-amb-torsor-with-section).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf.Torsor

/-- A torsor with a specified section over an object of the site.
Source: Stacks Project, Tag 03AJ, relative refinement
(blueprint: def-amb-torsor-with-section). -/
def WithSection {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (U : C) :=
  (P : Torsor G) × P.sheaf.obj.obj (op U)

/-- An isomorphism of pairs carries the specified section to the specified section.
Source: Stacks Project, Tag 03AJ, relative refinement
(blueprint: def-amb-torsor-with-section). -/
def WithSection.IsIsomorphic {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {G : Sheaf J AddCommGrpCat.{w}} {U : C} (P Q : WithSection G U) : Prop :=
  ∃ e : Torsor.Iso P.1 Q.1, e.iso.hom.hom.app (op U) P.2 = Q.2

/-- Isomorphism of pairs is an equivalence relation.
Source: Stacks Project, Tag 03AJ, relative refinement
(blueprint: def-amb-torsor-with-section).
Proof: the identity carries each section to itself; inverse and composite torsor
isomorphisms respectively reverse and compose the equality of specified sections. -/
theorem WithSection.isIsomorphic_equivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (G : Sheaf J AddCommGrpCat.{w}) (U : C) :
    _root_.Equivalence (@WithSection.IsIsomorphic C _ J G U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P
    exact ⟨Iso.refl P.1, rfl⟩
  · rintro P Q ⟨e, he⟩
    refine ⟨e.symm, ?_⟩
    change e.iso.inv.hom.app (op U) Q.2 = P.2
    rw [← he]
    exact CategoryTheory.Iso.hom_inv_id_apply
      (((sheafSections J (Type w)).obj (op U)).mapIso e.iso) P.2
  · rintro P Q R ⟨e, he⟩ ⟨f, hf⟩
    refine ⟨e.trans f, ?_⟩
    change f.iso.hom.hom.app (op U) (e.iso.hom.hom.app (op U) P.2) = R.2
    rw [he, hf]

/-- The setoid of section-preserving torsor isomorphisms.
Source: Stacks Project, Tag 03AJ, relative refinement
(blueprint: def-amb-torsor-with-section). -/
def WithSection.setoid {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (U : C) : Setoid (WithSection G U) where
  r := WithSection.IsIsomorphic
  iseqv := WithSection.isIsomorphic_equivalence G U

/-- Isomorphism classes of torsors with a specified section.
Source: Stacks Project, Tag 03AJ, relative refinement
(blueprint: def-amb-torsor-with-section). -/
def WithSection.Classes {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (G : Sheaf J AddCommGrpCat.{w}) (U : C) :=
  _root_.Quotient (WithSection.setoid G U)

end CategoryTheory.Sheaf.Torsor
