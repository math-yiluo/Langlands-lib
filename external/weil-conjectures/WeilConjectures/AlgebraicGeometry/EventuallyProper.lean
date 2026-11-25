/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ChowFiniteType
import WeilConjectures.AlgebraicGeometry.ClosedChowStage
import WeilConjectures.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap

/-!
# Properness descends to a finite stage

Source: Stacks Project, Limits, Lemma 081F in Situation 081D
(blueprint: lem-weil-pbc-eventually-proper).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A locally finite type morphism between qcqs schemes over a qcqs stage of an inverse
system with affine transitions is proper at some later stage if its base change to the
limit is proper. The distinguished index `i₀` need not be a least element.

Source: Stacks Project, Limits, Lemma 081F in Situation 081D
(blueprint: lem-weil-pbc-eventually-proper).

Proof:
1. By lem-weil-pbc-descend-separated (01ZQ), properness at the limit gives a separated
   stage i₁ ≥ i₀. Rebase there: affine transitions are quasi-compact and separated and
   remain affine under base change (lem-weil-pbc-affine-morphism-permanence).
   Thus the new base and source and target are qcqs
   (lem-weil-pbc-qcqs-morphism-permanence). Transitivity of fibre products identifies
   all later base changes with the original ones (def-pc-fibre-product), and local finite
   type persists (lem-weil-pbc-lft-base-change). We may assume f₀ separated.
2. The qcqs hypotheses make f₀ quasi-compact (lem-weil-pbc-qcqs-morphism-permanence,
   03GI), hence finite type. Chow's lemma (lem-weil-pbc-chow-finite-type, 0202) gives
   a proper surjection π₀ : X'₀ → X₀ and an immersion j₀ : X'₀ → Pⁿ over Y₀.
   The projective-space projection is proper
   (lemma-nagata-projective-space-base-change-proper).
3. Base change this diagram to every Sᵢ and to S. Pasting cartesian squares identifies
   X'₀ × over Y₀ with X'₀ × over S₀, and identifies projective space with the corresponding
   base-changed projective space (def-pc-fibre-product,
   def-nagata-projective-space-base-change). The maps j remain immersions
   (lem-weil-pbc-immersion-base-change-lft), while π remains proper and surjective
   (lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-surjective-base-change).
4. At the limit, fπ is proper by composition (lem-weil-pbc-proper-fp-permanence).
   Since projective space is separated over Y, j is proper
   (lem-weil-pbc-proper-over-separated, 01W6); a proper immersion is closed
   (lem-weil-pbc-proper-immersion-closed).
5. Apply lem-weil-pbc-descend-closed-immersion (01ZP) to j₀. Its source and target
   are qcqs because they are proper over qcqs schemes
   (lem-weil-pbc-qcqs-morphism-permanence); j₀ is locally finite type because it is
   an immersion (lem-weil-pbc-immersion-base-change-lft). Some jᵢ is a closed immersion.
6. Then jᵢ followed by the projective projection is proper
   (lem-weil-pbc-proper-fp-permanence,
   lemma-nagata-projective-space-base-change-proper). The map πᵢ is surjective and
   fᵢ is separated and finite type (lem-pod-separated-finite-type-base-change).
   Hence fᵢ is universally closed by lem-weil-pbc-image-universally-closed (03GN),
   and therefore proper. The index found after rebasing also satisfies i ≥ i₀. -/
theorem exists_isProper_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (a : X₀ ⟶ D.obj (op i₀)) (b : Y₀ ⟶ D.obj (op i₀))
    (f₀ : X₀ ⟶ Y₀) (h : f₀ ≫ b = a) [LocallyOfFiniteType f₀]
    (hf : IsProper (pullback.map a (c.π.app (op i₀)) b (c.π.app (op i₀))
      f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
      ((Category.comp_id a).trans h.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsProper (pullback.map a (D.map (homOfLE hi).op) b (D.map (homOfLE hi).op)
        f₀ (𝟙 (D.obj (op i))) (𝟙 (D.obj (op i₀)))
        ((Category.comp_id a).trans h.symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  let X : Over (D.obj (op i₀)) := Over.mk a
  let Y : Over (D.obj (op i₀)) := Over.mk b
  let f : X ⟶ Y := Over.homMk f₀ h
  have : CompactSpace X.left := inferInstanceAs (CompactSpace X₀)
  have : QuasiSeparatedSpace X.left := inferInstanceAs (QuasiSeparatedSpace X₀)
  have : CompactSpace Y.left := inferInstanceAs (CompactSpace Y₀)
  have : QuasiSeparatedSpace Y.left := inferInstanceAs (QuasiSeparatedSpace Y₀)
  have : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType f₀)
  have hf' : IsProper (((Over.pullback (c.π.app (op i₀))).map f).left) := by
    simpa [X, Y, f, Over.pullback, pullback.map] using hf
  have hsep : IsSeparated (((Over.pullback (c.π.app (op i₀))).map f).left) :=
    hf'.toIsSeparated
  obtain ⟨i₁, h₁, hsep₁⟩ := Scheme.exists_isSeparated_overPullbackMap D c hc i₀ X Y f hsep
  let B := Over.pullback (D.map (homOfLE h₁).op)
  have : IsSeparated (B.map f).left := hsep₁
  have : LocallyOfFiniteType (B.map f).left :=
    MorphismProperty.overPullbackMap _ f (inferInstance : LocallyOfFiniteType f.left)
  have : CompactSpace (B.obj Y).left := by dsimp [B, Y, Over.pullback]; infer_instance
  have : QuasiSeparatedSpace (B.obj Y).left := by
    dsimp [B, Y, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace (B.obj X).left := by dsimp [B, X, Over.pullback]; infer_instance
  obtain ⟨n, T₁, π₁, j₁, hπ₁, hsurj₁, hj₁, hw₁⟩ := exists_chow_finite_type (B.map f).left
  obtain ⟨i, h₁i, π, j, hsurj, hj, hw, hsepᵢ⟩ :=
    exists_closed_chow_stage D c hc i₀ X Y f hf' i₁ h₁ hsep₁
      n T₁ π₁ j₁ hπ₁ hsurj₁ hj₁ hw₁
  let Bi := Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)
  have : Surjective π := hsurj
  have : IsClosedImmersion j := hj
  have : IsProper (π ≫ (Bi.map f).left) := by
    rw [← hw]
    infer_instance
  have : IsSeparated (Bi.map f).left := hsepᵢ
  have : LocallyOfFiniteType (Bi.map f).left :=
    MorphismProperty.overPullbackMap _ f (inferInstance : LocallyOfFiniteType f.left)
  have hp : IsProper (Bi.map f).left := by
    rw [isProper_iff]
    exact ⟨inferInstance, UniversallyClosed.of_comp_surjective π _, inferInstance⟩
  refine ⟨i, h₁.trans h₁i, ?_⟩
  simpa [Bi, X, Y, f, Over.pullback, pullback.map] using hp

end AlgebraicGeometry
