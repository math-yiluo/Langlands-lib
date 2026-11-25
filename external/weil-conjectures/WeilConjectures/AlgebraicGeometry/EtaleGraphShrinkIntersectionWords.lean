/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords

/-! # The common intersection word for a shrinking graph neighborhood

Source: Stacks Project, Tag 0F7J, intersection calculation in the independence
of choices argument (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.EtaleGraphPresentation

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

variable {X Z : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
  (H : EtaleGraphPresentation h)

/-- Intersection of the two open graph neighborhoods. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphIntersection :=
  pullback (pullback.fst (pullback.snd H.p c.g) c.i)
    (pullback.fst (pullback.fst H.p c.g) H.e)

/-- The graph in the intersection, constructed by its two projections.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphS₁₂ := locallyClosedGraphS₁₂ H.a H.e H.p c.i c.g (H.graphEquation c)

/-- Properness follows from the proper first graph and its separated open projection.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance graphS₁₂_proper : IsProper (H.graphS₁₂ c) := by
  have : IsProper (H.graphS₁₂ c ≫ pullback.fst _ _) := by
    simpa only [graphS₁₂, locallyClosedGraphS₁₂, pullback.lift_fst] using
      (inferInstance : IsProper (H.graphS₁ c))
  exact IsProper.of_comp _ (pullback.fst _ _)

/-- The common open inclusion, written using the first projection.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphIntersectionOpen :=
  pullback.fst (pullback.fst (pullback.snd H.p c.g) c.i)
    (pullback.fst (pullback.fst H.p c.g) H.e) ≫
      pullback.fst (pullback.snd H.p c.g) c.i

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The intermediate word on the intersection, before either triangle is cancelled.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev graphIntersectionWord :=
  R((H.graphS₁₂ c)_*[ModuleCat.{u + 1} A]) ⋙
    D((H.graphIntersectionOpen c)_!open[ModuleCat.{u + 1} A]) ⋙
      R((pullback.fst H.p c.g ≫ H.p)_*[ModuleCat.{u + 1} A])

/-- The inverse first triangle and the open compositor, under the ambient proper image.
Source: Stacks Tag 0F7J, first half of the intersection word
(auxiliary; not a blueprint node). -/
def graphIntersectionLeg₁ : H.graphFirstWord c A ≅ H.graphIntersectionWord c A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
            (H.graphS₁₂ c) (pullback.fst _ _) (H.graphS₁ c)
            (by dsimp only [graphS₁₂, locallyClosedGraphS₁₂]; simp)).symm _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) (pullback.fst _ _) (pullback.fst _ _)).symm) _ ≪≫
    Functor.associator _ _ _

/-- The pullback equality, the second open compositor, and the second triangle.
Source: Stacks Tag 0F7J, second half of the intersection word
(auxiliary; not a blueprint node). -/
def graphIntersectionLeg₂ : H.graphIntersectionWord c A ≅ H.graphSecondWord c A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _
          (mapDerivedCategoryOpenImmersionLowerShriekCongr
              (ModuleCat.{u + 1} A) pullback.condition ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) (pullback.snd _ _) (pullback.fst _ _)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
            (H.graphS₁₂ c) (pullback.snd _ _) (H.graphS₂ c)
            (by dsimp only [graphS₁₂, locallyClosedGraphS₁₂]; simp)) _) _ ≪≫
    Functor.associator _ _ _

/-- The middle word is the composite of its two intersection legs.
Source: Stacks Tag 0F7J, the displayed intersection composite
(auxiliary; not a blueprint node). -/
theorem graphMiddle_eq_intersectionLegs :
    (H.graphMiddle c A).hom =
      (H.graphIntersectionLeg₁ c A).hom ≫ (H.graphIntersectionLeg₂ c A).hom := by
  ext M
  simp only [graphMiddle, graphIntersectionLeg₁, graphIntersectionLeg₂,
    locallyClosedGraphMiddle, graphS₁₂, graphS₁, graphS₂, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.assoc, Category.id_comp, Category.comp_id]

variable {W : Scheme.{u}} (a' : X ⟶ W) (v : W ⟶ H.U)
  [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a)

/-- The map of intersections induced by the smaller second neighborhood.
Source: Stacks Tag 0F7J, pullback of the neighborhood inclusion
(auxiliary; not a blueprint node). -/
def graphIntersectionShrink :
    (H.shrink a' v fac).graphIntersection c ⟶ H.graphIntersection c :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ H.graphNeighborhoodShrink c a' v fac)
    (by rw [Category.assoc, H.graphNeighborhoodShrink_open_fac c a' v fac]
        exact pullback.condition)

/-- The first intersection projection is unchanged under shrinking.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem graphIntersectionShrink_fst :
    H.graphIntersectionShrink c a' v fac ≫ pullback.fst _ _ =
      pullback.fst (pullback.fst (pullback.snd H.p c.g) c.i)
        (pullback.fst (pullback.fst H.p c.g) (v ≫ H.e)) := by
  dsimp only [graphIntersectionShrink, shrink]
  exact pullback.lift_fst _ _ _

/-- The second projection commutes with the smaller-neighborhood inclusion.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem graphIntersectionShrink_snd :
    H.graphIntersectionShrink c a' v fac ≫ pullback.snd _ _ =
      pullback.snd (pullback.fst (pullback.snd H.p c.g) c.i)
        (pullback.fst (pullback.fst H.p c.g) (v ≫ H.e)) ≫
          H.graphNeighborhoodShrink c a' v fac := by
  dsimp only [graphIntersectionShrink, shrink]
  exact pullback.lift_snd _ _ _

/-- The intersection inclusion is the base change of the neighborhood inclusion.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem graphIntersectionShrink_isPullback :
    IsPullback (H.graphIntersectionShrink c a' v fac) (pullback.snd _ _)
      (pullback.snd _ _) (H.graphNeighborhoodShrink c a' v fac) := by
  dsimp only [graphIntersection, shrink]
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := pullback.fst _ _) (v₁₃ := pullback.fst (pullback.snd H.p c.g) c.i)
  · rw [H.graphNeighborhoodShrink_open_fac c a' v fac]
    dsimp only [graphIntersectionShrink, shrink]
    simpa only [pullback.lift_fst] using
      (IsPullback.of_hasPullback (pullback.fst (pullback.snd H.p c.g) c.i)
        (pullback.fst (pullback.fst H.p c.g) (v ≫ H.e)))
  · dsimp only [graphIntersectionShrink, shrink]
    simp only [pullback.lift_snd]
  · exact IsPullback.of_hasPullback _ _

/-- Base change makes the map of intersections open. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
instance graphIntersectionShrink_open :
    IsOpenImmersion (H.graphIntersectionShrink c a' v fac) :=
  MorphismProperty.of_isPullback
    (H.graphIntersectionShrink_isPullback c a' v fac).flip inferInstance

/-- Both coordinates of the smaller intersection graph equal those of the old graph.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem graphIntersectionShrink_graph :
    (H.shrink a' v fac).graphS₁₂ c ≫ H.graphIntersectionShrink c a' v fac =
      H.graphS₁₂ c := by
  apply pullback.hom_ext
  · simp only [Category.assoc, graphIntersectionShrink, pullback.lift_fst]
    dsimp only [graphS₁₂, locallyClosedGraphS₁₂]
    simpa only [pullback.lift_fst] using H.graphFirstLift_shrink c a' v fac
  · simp only [Category.assoc, graphIntersectionShrink, pullback.lift_snd]
    dsimp only [graphS₁₂, locallyClosedGraphS₁₂]
    simpa only [pullback.lift_snd_assoc, pullback.lift_snd] using
      H.graphNeighborhoodShrink_graph c a' v fac

/-- The open inclusion into the common ambient product commutes with shrinking.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
theorem graphIntersectionShrink_open_fac :
    H.graphIntersectionShrink c a' v fac ≫ H.graphIntersectionOpen c =
      (H.shrink a' v fac).graphIntersectionOpen c := by
  dsimp only [graphIntersectionOpen, graphIntersectionShrink, shrink]
  simp only [← Category.assoc, pullback.lift_fst]

/-- The specified inverse triangle on the common intersection, followed by open composition.
Source: Stacks Tag 0F7J, cancellation of the smaller intersection triangle
(auxiliary; not a blueprint node). -/
def graphIntersectionShrinkIso :
    H.graphIntersectionWord c A ≅ (H.shrink a' v fac).graphIntersectionWord c A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
        ((H.shrink a' v fac).graphS₁₂ c) (H.graphIntersectionShrink c a' v fac)
        (H.graphS₁₂ c) (H.graphIntersectionShrink_graph c a' v fac)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (H.graphIntersectionShrink c a' v fac) (H.graphIntersectionOpen c)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (H.graphIntersectionShrink_open_fac c a' v fac)) _)

end AlgebraicGeometry.Etale.EtaleGraphPresentation
