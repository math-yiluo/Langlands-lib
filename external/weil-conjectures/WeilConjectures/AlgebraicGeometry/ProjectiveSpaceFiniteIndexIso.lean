/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso

/-! # Reindexing finite projective space and its twisting module

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-finite-index-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- A nonempty finite coordinate type can be replaced by `ULift (Fin (n + 1))`,
compatibly with the structure map and the twisting module.

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-finite-index-iso).

Proof:
1. Write the positive cardinality of the finite nonempty type as n + 1, and choose
   b : ULift (Fin (n + 1)) ≃ β using Fintype.equivFinOfCardEq and Equiv.ulift.
2. Reorder the coordinate sections of the identity pullback of O(1) by b. They are
   free generators on the reordered standard opens, which cover by Equiv.iSup_comp.
   Apply homOfIsFreeGenerator and the reindexing invertibility lemma to get e.
   The native homOfIsFreeGenerator_over gives the equality of structure maps.
3. The native twistRestrictHom is an isomorphism from e^* O(1) to the identity
   pullback of O(1). Compose it with pullbackId to obtain e^* O(1) ≅ O(1). -/
theorem exists_finite_index_iso (β : Type u) [Finite β] [Nonempty β] (S : Scheme.{u}) :
    ∃ (n : ℕ) (e : ℙ(β; S) ≅ ℙ(ULift.{u} (Fin (n + 1)); S)),
      e.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = ℙ(β; S) ↘ S ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj
        (twist (ULift.{u} (Fin (n + 1))) S 1) ≅ twist β S 1) := by
  classical
  let _ := Fintype.ofFinite β
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card β))
  let γ := ULift.{u} (Fin (n + 1))
  let b : γ ≃ β := Equiv.ulift.trans (Fintype.equivFinOfCardEq hn).symm
  let s := fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
    (twistOneSection β S (b j))
  let U := fun j : γ ↦ standardOpen β S (b j)
  let hs := fun j : γ ↦
    isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
  have hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
  let φ := homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU
  have : IsIso φ := isIso_homOfIsFreeGenerator_reindex β γ b S
  refine ⟨n, asIso φ, homOfIsFreeGenerator_over s U hs _ hU, ?_⟩
  exact ⟨asIso (twistRestrictHom s U hs (ℙ(β; S) ↘ S) hU) ≪≫
    (Scheme.Modules.pullbackId ℙ(β; S)).app (twist β S 1)⟩

end AlgebraicGeometry.ProjectiveSpace
