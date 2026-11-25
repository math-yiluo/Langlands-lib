/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sets.Closeds

/-! # Support of direct image with closed ambient support

Source: Stacks Project, Lemma 0CYJ, proof.
(blueprint: new-closed-support-pushforward-support)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Direct image has support inside the given closed ambient support.
Source: Stacks Project, Lemma 0CYJ, proof (vanishing on the complement).
(blueprint: new-closed-support-pushforward-support)

Proof: At a point outside T, shrink each representative of a direct-image stalk
section to the complement of T. Its sections are sections of F on the inverse image.
Every stalk there is zero by the support hypothesis; the sheaf section extensionality
lemma makes each such section zero. Every germ at the original point is therefore zero.
This also covers empty schemes, empty supports and zero modules. -/
theorem pushforward_support_subset_of_closed_support
    {Y X : Scheme.{u}} (j : Y ⟶ X) (F : Y.Modules)
    (T : TopologicalSpace.Closeds X)
    (hSupp : {y : Y | ¬ Subsingleton (F.presheaf.stalk y)} ⊆
      j.base ⁻¹' (T : Set X)) :
    {x : X | ¬ Subsingleton (((pushforward j).obj F).presheaf.stalk x)} ⊆
      (T : Set X) := by
  classical
  intro x hx
  by_contra hxT
  apply hx
  let G := (pushforward j).obj F
  have hz (t : G.presheaf.stalk x) : t = 0 := by
    obtain ⟨V, hxV, s, rfl⟩ := G.presheaf.exists_germ_eq t
    let W := V ⊓ T.compl
    have hxW : x ∈ W := ⟨hxV, hxT⟩
    have hs : G.presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op s = 0 := by
      change F.presheaf.map _ s = 0
      apply TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩
      intro y hy
      have hyT : j y ∉ (T : Set X) := hy.2
      have : Subsingleton (F.presheaf.stalk y) := by
        by_contra hn
        exact hyT (hSupp hn)
      exact Subsingleton.elim _ _
    rw [← G.presheaf.germ_res_apply (homOfLE (show W ≤ V from inf_le_left)) x hxW s]
    rw [hs, map_zero]
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end AlgebraicGeometry.Scheme.Modules
