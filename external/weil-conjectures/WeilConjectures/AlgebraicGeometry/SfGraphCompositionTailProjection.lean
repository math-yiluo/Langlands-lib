/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import all WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import WeilConjectures.AlgebraicGeometry.SfGraphInterchangeProjection
import WeilConjectures.AlgebraicGeometry.SfGraphWordProjectionSquare

/-! # Projection along the remaining graph-composition word

Source: `LowerShriekComposition.lean`, graph construction, and Stacks Tags
0B56, 0GL1 and 0F7B. (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem projection_normalization_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G : D ⥤ E} {H H' : C ⥤ E}
    (a : F ≅ F') (b : H ≅ H') (e : F' ⋙ G ≅ H') (v : H ≅ F ⋙ G)
    (hv : v = b ≪≫ e.symm ≪≫ Functor.isoWhiskerRight a.symm G) (P : C) :
    v.hom.app P ≫ G.map (a.hom.app P) ≫ e.hom.app P = b.hom.app P := by
  have he : v ≪≫ Functor.isoWhiskerRight a G ≪≫ e = b := by
    rw [hv]
    simp only [Iso.trans_assoc, ← Functor.isoWhiskerRight_symm,
      Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  simpa only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using
      congrArg (fun i ↦ i.hom.app P) he

private theorem projection_interchange_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G : D ⥤ E} {H H' : C ⥤ E}
    (TD : D ⥤ D) (TE : E ⥤ E) (M N N' : C)
    (a : F ≅ F') (b : H ≅ H') (e : F' ⋙ G ≅ H') (v : H ≅ F ⋙ G)
    (hv : ∀ P, v.hom.app P ≫ G.map (a.hom.app P) ≫ e.hom.app P = b.hom.app P)
    (pf : TD.obj (F.obj M) ⟶ F.obj N) (pf' : TD.obj (F'.obj M) ⟶ F'.obj N)
    (ph : TE.obj (H.obj M) ⟶ H.obj N') (ph' : TE.obj (H'.obj M) ⟶ H'.obj N')
    (q : N' ⟶ N) (pg : G ⋙ TE ⟶ TD ⋙ G)
    (hf : TD.map (a.hom.app M) ≫ pf' = pf ≫ a.hom.app N)
    (hh : TE.map (b.hom.app M) ≫ ph' = ph ≫ b.hom.app N')
    (ht : pg.app (F'.obj M) ≫ G.map pf' ≫ e.hom.app N =
      TE.map (e.hom.app M) ≫ ph' ≫ H'.map q) :
    TE.map (v.hom.app M) ≫ pg.app (F.obj M) ≫ G.map pf =
      ph ≫ v.hom.app N' ≫ G.map (F.map q) := by
  have hgf := congrArg G.map hf
  simp only [Functor.map_comp] at hgf
  have hn := pg.naturality (a.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hq : v.hom.app N' ≫ G.map (F.map q) ≫ G.map (a.hom.app N) ≫
      e.hom.app N = b.hom.app N' ≫ H'.map q := by
    rw [← G.map_comp_assoc, a.hom.naturality q, G.map_comp_assoc]
    have he := e.hom.naturality q
    dsimp only [Functor.comp_map] at he
    rw [he]
    simpa only [Category.assoc] using congrArg (· ≫ H'.map q) (hv N')
  apply (cancel_mono (G.map (a.hom.app N) ≫ e.hom.app N)).1
  simp only [Category.assoc]
  rw [← reassoc_of% hgf, ← reassoc_of% hn, ht]
  rw [← TE.map_comp_assoc, ← TE.map_comp_assoc]
  simp only [Category.assoc, hv M]
  rw [reassoc_of% hh]
  exact congrArg (ph ≫ ·) hq.symm

private theorem projection_cancel_first_comparison
    {C E : Type*} [Category C] [Category E]
    {H H₀ F : C ⥤ E} (T : E ⥤ E) (M N N' : C)
    (a : H ≅ H₀) (v : H₀ ≅ F) (q : N' ⟶ N)
    (p : T.obj (H.obj M) ⟶ H.obj N')
    (p₀ : T.obj (H₀.obj M) ⟶ H₀.obj N')
    (r : T.obj (F.obj M) ⟶ F.obj N)
    (ha : T.map (a.hom.app M) ≫ p₀ = p ≫ a.hom.app N')
    (hv : T.map ((a ≪≫ v).hom.app M) ≫ r =
      p ≫ (a ≪≫ v).hom.app N' ≫ F.map q) :
    T.map (v.hom.app M) ≫ r = p₀ ≫ v.hom.app N' ≫ F.map q := by
  apply (cancel_epi (T.map (a.hom.app M))).1
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    reassoc_of% ha] using hv

private theorem projection_interchange_transport_tensor
    {C D E I J : Type*} [Category C] [Category D] [Category E]
    [Category I] [Category J]
    {F F' : C ⥤ D} {G : D ⥤ E} {H H' : C ⥤ E}
    (TD : D ⥤ I ⥤ D) (TE : E ⥤ J ⥤ E) (L : I) (K : J) (M N N' : C)
    (a : F ≅ F') (b : H ≅ H') (e : F' ⋙ G ≅ H') (v : H ≅ F ⋙ G)
    (hv : ∀ P, v.hom.app P ≫ G.map (a.hom.app P) ≫ e.hom.app P = b.hom.app P)
    (pf : (TD.obj (F.obj M)).obj L ⟶ F.obj N)
    (pf' : (TD.obj (F'.obj M)).obj L ⟶ F'.obj N)
    (ph : (TE.obj (H.obj M)).obj K ⟶ H.obj N')
    (ph' : (TE.obj (H'.obj M)).obj K ⟶ H'.obj N')
    (q : N' ⟶ N) (pg : G ⋙ TE.flip.obj K ⟶ TD.flip.obj L ⋙ G)
    (hf : (TD.map (a.hom.app M)).app L ≫ pf' = pf ≫ a.hom.app N)
    (hh : (TE.map (b.hom.app M)).app K ≫ ph' = ph ≫ b.hom.app N')
    (ht : pg.app (F'.obj M) ≫ G.map pf' ≫ e.hom.app N =
      (TE.map (e.hom.app M)).app K ≫ ph' ≫ H'.map q) :
    (TE.map (v.hom.app M)).app K ≫ pg.app (F.obj M) ≫ G.map pf =
      ph ≫ v.hom.app N' ≫ G.map (F.map q) := by
  exact projection_interchange_transport (TD.flip.obj L) (TE.flip.obj K)
    M N N' a b e v hv pf pf' ph ph' q pg hf hh ht

private theorem projection_cancel_first_comparison_tensor
    {C E J : Type*} [Category C] [Category E] [Category J]
    {H H₀ F : C ⥤ E} (T : E ⥤ J ⥤ E) (K : J) (M N N' : C)
    (a : H ≅ H₀) (v : H₀ ≅ F) (q : N' ⟶ N)
    (p : (T.obj (H.obj M)).obj K ⟶ H.obj N')
    (p₀ : (T.obj (H₀.obj M)).obj K ⟶ H₀.obj N')
    (r : (T.obj (F.obj M)).obj K ⟶ F.obj N)
    (ha : (T.map (a.hom.app M)).app K ≫ p₀ = p ≫ a.hom.app N')
    (hv : (T.map ((a ≪≫ v).hom.app M)).app K ≫ r =
      p ≫ (a ≪≫ v).hom.app N' ≫ F.map q) :
    (T.map (v.hom.app M)).app K ≫ r = p₀ ≫ v.hom.app N' ≫ F.map q := by
  exact projection_cancel_first_comparison (T.flip.obj K) M N N' a v q p p₀ r ha hv

namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] EtaleGraphPresentation.functor
  EtaleGraphInterchangeDiagram.sourcePresentation
  EtaleGraphInterchangeDiagram.compositePresentation
attribute [local implicit_reducible] graphDiagram
  EtaleGraphInterchangeDiagram.compactification
attribute [local irreducible] sfGraphCompactSupportCompIso
  sfGraphCompactificationComparison etaleGraphComparisonFromOpen
  sfGraphWordProjection sfGraphCompositionTailIso projectionMapOfCompactification
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory derivedTensor
  upperStar lowerStar openImmersionLowerShriek
attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local irreducible] diagramCompIso diagramRawInterchange

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem diagram_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (ch : Compactification (f ≫ g))
    (d : EtaleGraphInterchangeDiagram f g) (sq : IsPullback d.r d.k d.i d.p)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat.{u + 1} A) Z).map
      ((diagramCompIso A cf ch d).hom.app M)).app K ≫
      sfCompactProjection A d.compactification
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        d.compactification).map (sfCompactProjection A cf M
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)) =
    sfCompactProjection A ch M K ≫ (diagramCompIso A cf ch d).hom.app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor.obj K)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        d.compactification).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))) := by
  let a := sfGraphPresentationComparison A cf d.sourcePresentation
  let b := sfGraphPresentationComparison A ch d.compositePresentation
  let v := diagramCompIso A cf ch d
  have hv : v = b ≪≫ (diagramRawInterchange A d).symm ≪≫
      Functor.isoWhiskerRight a.symm
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d.compactification) := by
    simpa only [v, a, b, sfGraphPresentationComparison,
      sfComparison_eq_graphComparison] using diagramCompIso_raw A cf ch d
  have hv' (P : DerivedCategoryModule A X) :
      v.hom.app P ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d.compactification).map
            (a.hom.app P) ≫
          (diagramRawInterchange A d).hom.app P = b.hom.app P :=
    projection_normalization_app a b (diagramRawInterchange A d) v hv P
  have hi := sfGraphInterchange_projection A d
    sq M K
  have hI : Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
      (etaleGraphOpenNormalization A d.compactification).symm ≪≫
        etaleGraphDiagramInterchange A d = diagramRawInterchange A d := by
    simp only [etaleGraphDiagramInterchange, diagramRawInterchange,
      ← Functor.isoWhiskerLeft_symm, Iso.symm_self_id_assoc]
  dsimp only at hi
  rw [hI] at hi
  have hp := projection_interchange_transport_tensor
    (derivedTensor (ModuleCat.{u + 1} A) Y) (derivedTensor (ModuleCat.{u + 1} A) Z)
    ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) K M
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
      ((upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor.obj K))
    a b (diagramRawInterchange A d) v hv'
    (sfCompactProjection A cf M ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (sfGraphWordProjection A d.sourcePresentation M
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (sfCompactProjection A ch M K) (sfGraphWordProjection A d.compositePresentation M K)
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))
    (((flipFunctor _ _ _).map
      (projectionMapOfCompactification (ModuleCat.{u + 1} A) d.compactification)).app K)
    (sfGraphCompactificationComparison_projection A cf d.sourcePresentation M
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (sfGraphCompactificationComparison_projection A ch d.compositePresentation M K) hi
  exact hp

/-- Projection compatibility for the tail of the graph composition word.

Source: node lem-sf-etale-compact-projection-coherence, steps 6--7;
`LowerShriekComposition.lean`, e3 followed by inverse e2; Stacks Tags 0B56,
0GL1 and 0F7B. (auxiliary; not a blueprint node).

Proof: apply the Cartesian graph-interchange projection square to the explicit
product graph diagram. Normalize the actual compact-support compositor as the
composite graph comparison, inverse raw interchange and inverse source graph
comparison. Paste the projection squares for the source and composite graph
comparisons with the interchange square. Naturality of these comparisons and
cancellation of their isomorphisms give the full compositor projection square.
Factor that compositor as the first graph comparison followed by the specified
tail. Paste the first graph comparison's projection square and cancel tensoring
that comparison. The remaining equality is precisely the stated tail square.
Only graph comparison isomorphisms are cancelled; no projection map is inverted.
The calculation applies to arbitrary schemes and unbounded complexes, including
empty and identity opens and zero coefficients.
-/
theorem sfGraphCompositionTailIso_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g))
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat.{u + 1} A) Z).map
        ((sfGraphCompositionTailIso A f g cf cg ch).hom.app M)).app K ≫
      sfCompactProjection A cg
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (sfCompactProjection A cf M
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)) =
    sfGraphWordProjection A (sfCompositionGraphPresentation f g cg ch) M K ≫
      (sfGraphCompositionTailIso A f g cf cg ch).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor.obj K)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))) := by
  let d := graphDiagram f g cg ch
  have hp := diagram_projection A cf ch d
    (IsPullback.of_hasPullback d.p d.i).flip M K
  rw [← graphCompositor_normalization A f g cf cg ch] at hp
  simp only [d, graphDiagram_compactification] at hp
  have hp' := projection_cancel_first_comparison_tensor
    (derivedTensor (ModuleCat.{u + 1} A) Z) K M
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
      ((upperStar (ModuleCat.{u + 1} A) (f ≫ g)).leftDerivedFunctor.obj K))
    (sfGraphPresentationComparison A ch (sfCompositionGraphPresentation f g cg ch))
    (sfGraphCompositionTailIso A f g cf cg ch)
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))
    (sfCompactProjection A ch M K)
    (sfGraphWordProjection A (sfCompositionGraphPresentation f g cg ch) M K)
    (sfCompactProjection A cg
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) K ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        (sfCompactProjection A cf M ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)))
    (sfGraphCompactificationComparison_projection A ch
      (sfCompositionGraphPresentation f g cg ch) M K)
    (by rw [← sfGraphCompactSupportCompIso_factor]; exact hp)
  exact hp'

end AlgebraicGeometry.Etale
