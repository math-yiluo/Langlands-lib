/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry

/-! # The three words in the graph comparison and their shrinking map

Source: Stacks Project, Tag 0F7J, graph neighborhood calculation
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

namespace EtaleGraphPresentation

variable {X Z : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
  (H : EtaleGraphPresentation h)

/-- The equation used in the fixed graph construction. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem graphEquation : (H.a ≫ H.e) ≫ H.p = c.i ≫ c.g :=
  (Category.assoc _ _ _).trans (H.fac.trans c.comm)

/-- The first proper graph in the fixed product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphS₁ := locallyClosedGraphS₁ H.a H.e H.p c.i c.g (H.graphEquation c)

/-- The second proper graph in the fixed product. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphS₂ := locallyClosedGraphS₂ H.a H.e H.p c.i c.g (H.graphEquation c)

/-- The properness proof supplied by the graph model, with no choice of arrow.
Source: Stacks Tag 0F7B (auxiliary; not a blueprint node). -/
instance graphS₁_proper : IsProper (H.graphS₁ c) := by
  have he : H.graphS₁ c ≫ pullback.snd (pullback.snd H.p c.g) c.i = 𝟙 X := by
    dsimp only [graphS₁, locallyClosedGraphS₁]
    exact pullback.lift_snd _ _ _
  have : IsProper (H.graphS₁ c ≫ pullback.snd (pullback.snd H.p c.g) c.i) := by
    rw [he]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd (pullback.snd H.p c.g) c.i)

/-- The properness proof supplied by the graph model, with no choice of arrow.
Source: Stacks Tag 0F7B (auxiliary; not a blueprint node). -/
instance graphS₂_proper : IsProper (H.graphS₂ c) := by
  have he : H.graphS₂ c ≫ pullback.snd (pullback.fst H.p c.g) H.e = H.a := by
    dsimp only [graphS₂, locallyClosedGraphS₂]
    exact pullback.lift_snd _ _ _
  have : IsProper (H.graphS₂ c ≫ pullback.snd (pullback.fst H.p c.g) H.e) := by
    rw [he]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd (pullback.fst H.p c.g) H.e)

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The first neighborhood word. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphFirstWord :=
  R((H.graphS₁ c)_*[ModuleCat.{u + 1} A]) ⋙
    D((pullback.fst (pullback.snd H.p c.g) c.i)_!open[ModuleCat.{u + 1} A]) ⋙
      R((pullback.fst H.p c.g ≫ H.p)_*[ModuleCat.{u + 1} A])

/-- The second neighborhood word. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphSecondWord :=
  R((H.graphS₂ c)_*[ModuleCat.{u + 1} A]) ⋙
    D((pullback.fst (pullback.fst H.p c.g) H.e)_!open[ModuleCat.{u + 1} A]) ⋙
      R((pullback.fst H.p c.g ≫ H.p)_*[ModuleCat.{u + 1} A])

/-- The first side of the graph comparison. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphSide₁ := locallyClosedGraphSide₁ H.a H.e H.p c.i c.g (H.graphEquation c) A

/-- The second side of the graph comparison. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphSide₂ := locallyClosedGraphSide₂ H.a H.e H.p c.i c.g (H.graphEquation c) A

/-- The middle graph word with its two associators. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def graphMiddle : H.graphFirstWord c A ≅ H.graphSecondWord c A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (locallyClosedGraphMiddle H.a H.e H.p c.i c.g (H.graphEquation c) A) _ ≪≫
    Functor.associator _ _ _

variable {W : Scheme.{u}} (a' : X ⟶ W) (v : W ⟶ H.U)
  [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a)

/-- The first graph lift is unchanged when the neighborhood is shrunk.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node).
Proof: the two ambient coordinates are a e = a' v e and the same map j to c. -/
theorem graphFirstLift_shrink :
    (H.shrink a' v fac).graphS₁ c = H.graphS₁ c := by
  dsimp only [graphS₁, locallyClosedGraphS₁, shrink]
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
    dsimp only [locallyClosedGraphV, shrink]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, ← Category.assoc, fac]
    · simp only [pullback.lift_snd]
  · simp only [pullback.lift_snd]

/-- The identification of the first neighborhood words supplied by their common source.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def graphFirstShrinkIso :
    H.graphFirstWord c A ≅ (H.shrink a' v fac).graphFirstWord c A :=
  (H.graphSide₁ c A).symm ≪≫ (H.shrink a' v fac).graphSide₁ c A

/-- The specified inverse triangle on the second neighborhood, with its open compositor.
Source: Stacks Tag 0F7J (auxiliary; not a blueprint node). -/
def graphNeighborhoodTriangle :
    H.graphSecondWord c A ≅ (H.shrink a' v fac).graphSecondWord c A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        ((H.shrink a' v fac).graphS₂ c) (H.graphNeighborhoodShrink c a' v fac)
        (H.graphS₂ c) (H.graphNeighborhoodShrink_graph c a' v fac)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (H.graphNeighborhoodShrink c a' v fac) (pullback.fst _ _)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (H.graphNeighborhoodShrink_open_fac c a' v fac)) _)

end EtaleGraphPresentation

end AlgebraicGeometry.Etale
