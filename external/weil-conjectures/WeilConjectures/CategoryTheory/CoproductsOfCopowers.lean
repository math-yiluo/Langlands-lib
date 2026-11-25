/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Coproduct preservation from copower preservation

Source: the retract argument for coproduct comparison maps, written by V3.
-/

@[expose] public section

universe s uC vC uD vD

open CategoryTheory.Limits

namespace CategoryTheory

/-- A functor from a category with zero morphisms preserves coproducts if it preserves
sums of copies of one object, for every object.
Source: the elementary retract argument applied to the comparison morphisms.
(auxiliary; not a blueprint node)

Proof in words: given a family K_i, put S = coproduct K_i. Each K_i is a retract
of S, using its coprojection and the map equal to the identity on that summand
and zero on the others. These retracts give a retract of the whole diagram K
into the constant S diagram. Taking sums of their images, and taking the image
of their sums, gives a retract of the comparison map for K into the comparison
map for the constant S family. The latter is invertible by copower preservation.
An arrow retract of an isomorphism is an isomorphism, so the comparison for K
is invertible. Its invertibility is the coproduct preservation property.
For an empty family the diagram retract is the identity on the empty diagram. -/
theorem preservesCoproducts_of_preservesCopowers
    {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
    {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (I : Type s)
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I D]
    (hF : ∀ S : C, PreservesColimit (Discrete.functor (fun _ : I ↦ S)) F) :
    PreservesColimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → C) : PreservesColimit (Discrete.functor K) F := by
    let S := ∐ K
    let j : ∀ i, K i ⟶ S := Sigma.ι K
    let p : ∀ i, S ⟶ K i := fun i ↦
      Sigma.desc (fun k ↦ if h : k = i then eqToHom (congrArg K h) else 0)
    have hjp (i : I) : j i ≫ p i = 𝟙 (K i) := by simp [j, p]
    have : PreservesColimit (Discrete.functor (fun _ : I ↦ S)) F := hF S
    let r : RetractArrow (sigmaComparison F K)
        (sigmaComparison F (fun _ : I ↦ S)) :=
      { i := Arrow.homMk (Limits.Sigma.map (fun i ↦ F.map (j i))) (F.map (Limits.Sigma.map j)) (by
          dsimp only [Arrow.mk_hom]
          apply Sigma.hom_ext
          intro i
          simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison,
            ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_map])
        r := Arrow.homMk (Limits.Sigma.map (fun i ↦ F.map (p i))) (F.map (Limits.Sigma.map p)) (by
          dsimp only [Arrow.mk_hom]
          apply Sigma.hom_ext
          intro i
          simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison,
            ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_map])
        retract := by
          ext
          · simp only [Arrow.comp_left, Arrow.homMk_left, Arrow.id_left, Arrow.mk_left]
            rw [Sigma.map_comp_map]
            simp only [← Functor.map_comp, hjp, Functor.map_id, Sigma.map_id]
          · simp only [Arrow.comp_right, Arrow.homMk_right, Arrow.id_right, Arrow.mk_right]
            rw [← F.map_comp, Sigma.map_comp_map]
            simp only [hjp, Sigma.map_id, Functor.map_id] }
    have : IsIso (sigmaComparison F K) :=
      MorphismProperty.of_retract (P := MorphismProperty.isomorphisms D) r inferInstance
    exact PreservesCoproduct.of_iso_comparison F K
  let := h
  exact preservesColimitsOfShape_of_discrete F

end CategoryTheory
