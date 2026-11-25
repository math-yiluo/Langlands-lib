/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedIdealGenerators

/-!
# A cover with finite generating lists for an ideal sheaf

Source: Stacks Project, algebraization.tex, Tag 099E, first paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- Local finite type gives a covering family with an explicitly indexed finite generating
list on each slice. The indexing type of the covering stays in the universe of the site.
Source: Stacks Project, Tag 099E, first paragraph.
(auxiliary; not a blueprint node).

Proof: take Mathlib's local generators data of a finite-type module. Each generator
index type is finite; choose its equivalence with Fin of its cardinality. Apply the ideal
inclusion to the generator sections and evaluate them at the terminal object of the slice.
These are exactly the witnesses required by IsRingedIdealGeneratingList. The cover is
unchanged. Empty lists and an empty covering family require no separate assumption. -/
theorem exists_finiteIdealGeneratingCover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [I.IsFiniteType] :
    ∃ (A : Type u) (U : A → C) (r : A → ℕ)
      (f : ∀ a : A, Fin (r a) → O.obj.obj (op (U a))),
      J.CoversTop U ∧ ∀ a : A, IsRingedIdealGeneratingList O I ι (U a) (r a) (f a) := by
  classical
  obtain ⟨p, hp⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData I
  have (a : p.I) : (p.generators a).IsFiniteType := hp.isFiniteType a
  let (a : p.I) := Fintype.ofFinite (p.generators a).I
  let r (a : p.I) := Fintype.card (p.generators a).I
  let e (a : p.I) : (p.generators a).I ≃ Fin (r a) := Fintype.equivFin _
  let f (a : p.I) (i : Fin (r a)) : O.obj.obj (op (p.X a)) :=
    (SheafOfModules.sectionsMap (ι.over (p.X a))
      ((p.generators a).s ((e a).symm i))).val (op (Over.mk (𝟙 (p.X a))))
  refine ⟨p.I, p.X, r, f, p.coversTop, ?_⟩
  intro a
  refine ⟨p.generators a, e a, ?_⟩
  intro i
  dsimp only [f]
  rw [Equiv.symm_apply_apply]

/-- An object with a specified finite generating list for the restricted ideal.
Source: Stacks Project, Tag 099E, the finite-generator subsite.
(auxiliary; not a blueprint node). -/
structure RingedIdealGeneratingIndex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) where
  U : C
  r : ℕ
  f : Fin r → O.obj.obj (op U)
  generates : IsRingedIdealGeneratingList O I ι U r f

/-- All objects with specified finite generating lists form a covering family.
Source: Stacks Project, Tag 099E, first paragraph.
(auxiliary; not a blueprint node).

Proof: the finite generating cover gives a subfamily of this family. Enlarge its
covering sieves to the sieves of all objects carrying generating lists. -/
theorem coversTop_ringedIdealGeneratingIndex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [I.IsFiniteType] :
    J.CoversTop (fun p : RingedIdealGeneratingIndex O I ι ↦ p.U) := by
  obtain ⟨A, U, r, f, hU, hf⟩ := exists_finiteIdealGeneratingCover O I ι
  intro V
  apply J.superset_covering _ (hU V)
  rintro W g ⟨i, ⟨a⟩⟩
  exact ⟨⟨U i, r i, f i, hf i⟩, ⟨a⟩⟩

end CategoryTheory
