/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData

/-! # Neighborhood maps for a shrinking graph presentation

Source: Stacks Project, Tag 0F7J, product-graph neighborhood calculation
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

namespace EtaleGraphPresentation

variable {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
  (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
  [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a)

/-- The second neighborhood of the graph of a presentation. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphNeighborhood := pullback (pullback.fst H.p c.g) H.e

/-- The map on second graph neighborhoods induced by shrinking the supporting open.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def graphNeighborhoodShrink :
    (H.shrink a' v fac).graphNeighborhood c ⟶ H.graphNeighborhood c :=
  pullback.lift (pullback.fst (pullback.fst H.p c.g) (v ≫ H.e))
    (pullback.snd (pullback.fst H.p c.g) (v ≫ H.e) ≫ v)
    (by simpa only [graphNeighborhood, shrink, Category.assoc] using
      (pullback.condition (f := pullback.fst H.p c.g) (g := v ≫ H.e)))

/-- Shrinking the neighborhood is Cartesian over the original open immersion.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node).
Proof: the outside rectangle and the right square are the defining pullback squares;
cancel the right square. The two projection equations are those of pullback.lift. -/
theorem graphNeighborhoodShrink_isPullback :
    IsPullback (H.graphNeighborhoodShrink c a' v fac) (pullback.snd _ _)
      (pullback.snd _ _) v := by
  dsimp only [graphNeighborhood, shrink]
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := H.e) (v₁₃ := pullback.fst H.p c.g)
  · dsimp only [graphNeighborhoodShrink]
    simpa only [pullback.lift_fst] using
      (IsPullback.of_hasPullback (pullback.fst H.p c.g) (v ≫ H.e))
  · dsimp only [graphNeighborhoodShrink]
    simp only [pullback.lift_snd]
  · exact IsPullback.of_hasPullback (pullback.fst H.p c.g) H.e

/-- The induced neighborhood map is open by base change.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance graphNeighborhoodShrink_open :
    IsOpenImmersion (H.graphNeighborhoodShrink c a' v fac) :=
  MorphismProperty.of_isPullback
    (H.graphNeighborhoodShrink_isPullback c a' v fac).flip inferInstance

/-- The smaller graph followed by the induced open is exactly the larger graph.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node).
Proof: compare both projections; the ambient coordinate agrees since a' v = a,
and the supporting-open coordinate agrees by the same equality. -/
theorem graphNeighborhoodShrink_graph :
    locallyClosedGraphS₂ (H.shrink a' v fac).a (H.shrink a' v fac).e
        (H.shrink a' v fac).p c.i c.g
        ((Category.assoc (H.shrink a' v fac).a (H.shrink a' v fac).e
          (H.shrink a' v fac).p).trans ((H.shrink a' v fac).fac.trans c.comm)) ≫
      H.graphNeighborhoodShrink c a' v fac =
    locallyClosedGraphS₂ H.a H.e H.p c.i c.g
        ((Category.assoc H.a H.e H.p).trans (H.fac.trans c.comm)) := by
  dsimp only [graphNeighborhoodShrink, shrink, locallyClosedGraphS₂]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    dsimp only [locallyClosedGraphV]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, ← Category.assoc, fac]
    · simp only [pullback.lift_snd]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, fac, pullback.lift_snd]

/-- The induced map commutes with the ambient open inclusions. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node).
Proof: this is the first projection equation for the defining pullback lift. -/
theorem graphNeighborhoodShrink_open_fac :
    H.graphNeighborhoodShrink c a' v fac ≫ pullback.fst (pullback.fst H.p c.g) H.e =
      pullback.fst (pullback.fst H.p c.g) (v ≫ H.e) := by
  dsimp only [graphNeighborhoodShrink]
  simp only [pullback.lift_fst]

end EtaleGraphPresentation

end AlgebraicGeometry.Etale
