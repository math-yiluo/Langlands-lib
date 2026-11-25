/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.LocallySurjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Homology preservation by closed module pushforward

Source: Stacks Project, Modules, Tag 08KS.
(blueprint: lem-pc-closed-module-pushforward-homology). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open TopCat TopologicalSpace Topology Opposite

set_option backward.isDefEq.respectTransparency false in
private theorem closedPushforward_preservesEpimorphisms
    {X Y : TopCat.{u}} (i : X ⟶ Y) (hi : IsClosedEmbedding i) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).PreservesEpimorphisms := by
  constructor
  intro A B f hf
  rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
  replace hf := (TopCat.Presheaf.isLocallySurjective_iff f.hom).1 (by exact hf)
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun W t y hy ↦ ?_
  by_cases h : y ∈ Set.range i
  · obtain ⟨x, rfl⟩ := h
    obtain ⟨O, hOW, ⟨s, hs⟩, hxO⟩ := hf ((Opens.map i).obj W) t x hy
    obtain ⟨V, hV, hVO⟩ := hi.isInducing.isOpen_iff.mp O.isOpen
    let U : Opens Y := ⟨V, hV⟩ ⊓ W
    have hU : (Opens.map i).obj U ≤ O := by
      intro z hz
      change z ∈ (O : Set X)
      rw [← hVO]
      exact hz.1
    refine ⟨U, inf_le_right, ⟨A.obj.map (homOfLE hU).op s, ?_⟩, ?_⟩
    · change f.hom.app _ (A.obj.map _ s) = B.obj.map _ t
      rw [← ConcreteCategory.comp_apply, f.hom.naturality, ConcreteCategory.comp_apply, hs]
      change B.obj.map _ (B.obj.map _ t) = _
      erw [← ConcreteCategory.comp_apply, ← B.obj.map_comp]
      rfl
    · refine ⟨?_, hy⟩
      change x ∈ i ⁻¹' V
      rw [hVO]
      exact hxO
  · let U : Opens Y := W ⊓ ⟨(Set.range i)ᶜ, hi.isClosed_range.isOpen_compl⟩
    refine ⟨U, inf_le_left, ⟨0, ?_⟩, hy, h⟩
    have he : (Opens.map i).obj U = ⊥ := by
      ext x
      exact ⟨fun hx ↦ (hx.2 ⟨x, rfl⟩).elim, fun hx ↦ False.elim hx⟩
    have hz := AddCommGrpCat.subsingleton_of_isZero (B.isTerminalOfEqEmpty he).isZero
    exact @Subsingleton.elim (B.obj.obj (op ((Opens.map i).obj U))) hz _ _


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Closed-immersion pushforward of module sheaves preserves homology.

Source: Stacks Project, Modules, Lemma 17.13.4 (Tag 08KS).
(blueprint: lem-pc-closed-module-pushforward-homology).

Proof: An epimorphism of abelian sheaves is locally surjective. At a point in the
closed image, lift its section on a source neighbourhood, realize that neighbourhood
as the inverse image of an ambient open using the inducing property, and intersect
with the prescribed ambient neighbourhood. Restriction of the lift gives a local
lift there. At a point outside the image, use the open complement of the closed image;
its inverse image is empty, so the sheaf axiom makes the target sections zero and the
zero section is a lift. Thus abelian direct image preserves epimorphisms. The exact
faithful forgetful functor to abelian sheaves preserves and reflects epimorphisms,
and its composite with module direct image is definitionally the abelian direct
image. Module direct image therefore preserves epimorphisms. It is a right adjoint,
so preserves kernels. In abelian categories, these two properties imply preservation
of homology. Identity immersions and empty sources obey the same local argument. -/
theorem closed_modulePushforward_preservesHomology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    (Scheme.Modules.pushforward i).PreservesHomology := by
  have := closedPushforward_preservesEpimorphisms i.base i.isClosedEmbedding
  let F := Scheme.Modules.pushforward i
  have : F.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let G : Y.Modules ⥤ (Y : TopCat).Sheaf AddCommGrpCat.{u} :=
      SheafOfModules.toSheaf Y.ringCatSheaf
    have : G.Faithful := by
      exact inferInstanceAs (SheafOfModules.toSheaf Y.ringCatSheaf).Faithful
    apply G.epi_of_epi_map
    have hfg : Epi ((SheafOfModules.toSheaf Z.ringCatSheaf).map f) := by
      let GZ : Z.Modules ⥤ (Z : TopCat).Sheaf AddCommGrpCat.{u} :=
        SheafOfModules.toSheaf Z.ringCatSheaf
      have : GZ.PreservesEpimorphisms := by
        exact inferInstanceAs
          (SheafOfModules.toSheaf Z.ringCatSheaf).PreservesEpimorphisms
      exact Functor.map_epi GZ f
    change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map f))
    infer_instance
  exact Functor.preservesHomology_of_preservesEpis_and_kernels F


end AlgebraicGeometry
