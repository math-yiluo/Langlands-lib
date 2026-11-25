/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Stalks of pushforward along a closed immersion

Source: Stacks Project, Sheaves, Lemma 00AE and Modules, Lemma 08KS
(blueprint: lem-weil-pbc-closed-pushforward-stalks).
-/

@[expose] public section

universe w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

noncomputable section

/-- Stalks of the pushforward of a module along a morphism of schemes whose underlying map
is a closed embedding: (1) the stalk of `i_* G` vanishes off the closed image; (2) the germ map
`c_z = stalkPushforward : (i_* G)_{i(z)} → G_z` is bijective (an isomorphism) and linear over
`O_{X,i(z)}` acting on `G_z` through `i^♯_z = i.stalkMap z`; (3) `c_z` is natural in `G`.
Source: Stacks Project, Sheaves, Lemma 00AE and Modules, Lemma 08KS
(blueprint: lem-weil-pbc-closed-pushforward-stalks).
Proof: for `x ∉ i(Z)` the open `X \ i(Z)` is a neighbourhood of `x` with empty preimage, so
every germ is zero. For `z ∈ Z` the opens `i⁻¹V`, `V ∋ i(z)`, are cofinal among the
neighbourhoods of `z` (an open `U ∋ z` is `i⁻¹V` for `V = W ∪ (X \ i(Z))` with `W ∩ i(Z) = i(U)`),
so `c_z` is bijective; linearity is the germ rule `(a s)_z = i^♯(a_{i(z)}) s_z` for
`a ∈ O_X(V)`, `s ∈ G(i⁻¹V)`; naturality holds on germs.
-/
theorem closedImmersion_pushforward_stalks
    {X Z : Scheme.{w}} (i : Z ⟶ X)
    (h : Topology.IsClosedEmbedding i.base) (G : Z.Modules) :
    (∀ x : X, x ∉ Set.range i.base →
      Subsingleton (↥(TopCat.Presheaf.stalk ((Scheme.Modules.pushforward i).obj G).presheaf x))) ∧
    (∀ z : Z,
      Function.Bijective
        (ConcreteCategory.hom
          (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z)) ∧
      IsIso (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z) ∧
      ∀ (r : X.presheaf.stalk (i.base z))
        (m : ↥(TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward i).obj G).val.presheaf (i.base z))),
        ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base G.val.presheaf z)
            (r • m) =
          (i.stalkMap z).hom r •
            ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base G.val.presheaf z)
              m) ∧
    (∀ H : Z.Modules, ∀ φ : G ⟶ H, ∀ z : Z,
      (TopCat.Presheaf.stalkFunctor Ab (i.base z)).map
          ((Scheme.Modules.pushforward i).map φ).mapPresheaf ≫
          (TopCat.Presheaf.stalkPushforward Ab i.base H.presheaf z) =
        (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z) ≫
          (TopCat.Presheaf.stalkFunctor Ab z).map φ.mapPresheaf) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    let V : Opens X := ⟨(Set.range i.base)ᶜ, h.isClosed_range.isOpen_compl⟩
    have hxV : x ∈ V := hx
    let F := ((Scheme.Modules.pushforward i).obj G).presheaf
    have empty (U : Opens X) (hU : U ≤ V) : (Opens.map i.base).obj U = ⊥ := by
      ext z
      exact ⟨fun hz ↦ (hU hz) ⟨z, rfl⟩, False.elim⟩
    have trivial (U : Opens X) (hU : U ≤ V) : Subsingleton (F.obj (op U)) := by
      change Subsingleton (G.presheaf.obj (op ((Opens.map i.base).obj U)))
      exact AddCommGrpCat.subsingleton_of_isZero
        ((TopCat.Sheaf.isTerminalOfEqEmpty ⟨G.presheaf, G.isSheaf⟩ (empty U hU)).isZero)
    refine ⟨?_⟩
    intro a b
    obtain ⟨U, hUV, hxU, s, rfl⟩ := F.exists_le_germ_eq a hxV
    obtain ⟨W, hWV, hxW, t, rfl⟩ := F.exists_le_germ_eq b hxV
    let Q := U ⊓ W
    have hxQ : x ∈ Q := ⟨hxU, hxW⟩
    have := trivial Q (inf_le_left.trans hUV)
    have heq : F.map (homOfLE (inf_le_left : Q ≤ U)).op s =
        F.map (homOfLE (inf_le_right : Q ≤ W)).op t := Subsingleton.elim _ _
    rw [← F.germ_res_apply (homOfLE (inf_le_left : Q ≤ U)) x hxQ s,
      ← F.germ_res_apply (homOfLE (inf_le_right : Q ≤ W)) x hxQ t, heq]
  · intro z
    have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab
      h.isInducing G.presheaf z
    refine ⟨ConcreteCategory.bijective_of_isIso _, inferInstance, ?_⟩
    intro r m
    obtain ⟨U, hzU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hzV, m, rfl⟩ :=
      ((Scheme.Modules.pushforward i).obj G).presheaf.exists_le_germ_eq m hzU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) (i.base z) hzV r]
    erw [← PresheafOfModules.germ_smul ((Scheme.Modules.pushforward i).obj G).val]
    erw [TopCat.Presheaf.stalkPushforward_germ_apply,
      TopCat.Presheaf.stalkPushforward_germ_apply]
    change TopCat.Presheaf.germ G.val.presheaf (i ⁻¹ᵁ V) z hzV
        ((i.app V).hom (X.presheaf.map (homOfLE hVU).op r) •
          (show G.presheaf.obj (op (i ⁻¹ᵁ V)) from m)) = _
    erw [PresheafOfModules.germ_smul G.val]
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl
  · intro H φ z
    change (TopCat.Presheaf.stalkFunctor Ab (i.base z)).map
        ((TopCat.Presheaf.pushforward Ab i.base).map φ.mapPresheaf) ≫ _ = _
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hzU
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
      TopCat.Presheaf.stalkPushforward_germ,
      ← Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
      TopCat.Presheaf.stalkFunctor_map_germ]
    rfl

end
end AlgebraicGeometry
