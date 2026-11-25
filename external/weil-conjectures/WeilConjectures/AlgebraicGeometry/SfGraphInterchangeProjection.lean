/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import all WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange

/-! # Projection compatibility of one proper/open interchange

Source: Stacks Tags 0F7B, 0GL1, 0B56 and 0E48; the Cartesian interchange part
of `LowerShriekComposition.lean`, e3.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.comp
attribute [local irreducible] projectionMapOfCompactification rightDerivedLowerStarComp
  openImmersionLowerShriekLowerStarExchange mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekCongr

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedTensor rightDerivedLowerStarProjectionMap
  derivedOpenImmersionLowerShriekProjectionIso leftDerivedUpperStarComp
  upperStar lowerStar openImmersionLowerShriek

attribute [local implicit_reducible] EtaleGraphPresentation.functor

private theorem coefficient_transport_grouped
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {T : C ⥤ C} {U : D ⥤ D} {L : D ⥤ C}
    {Y Y' : D} {N N' : C} {W : E}
    {c : Y ⟶ Y'} {v : L.obj Y' ⟶ N'} {w : L.obj Y ⟶ N} {d : N ⟶ N'}
    {a : U.obj Y ⟶ F.obj (T.obj (L.obj Y))}
    {a' : U.obj Y' ⟶ F.obj (T.obj (L.obj Y'))}
    (ha : U.map c ≫ a' = a ≫ F.map (T.map (L.map c)))
    (hv : L.map c ≫ v = w ≫ d) (p : W ⟶ G.obj (U.obj Y)) :
    p ≫ G.map (U.map c) ≫ G.map (a' ≫ F.map (T.map v)) =
      p ≫ G.map (a ≫ F.map (T.map w)) ≫ G.map (F.map (T.map d)) := by
  simpa only [Functor.map_comp, Category.assoc] using
    projection_coefficient_transport ha hv p

private theorem interchange_prefix_transport
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ V} {J : D ⥤ V}
    (e : G ⋙ H ≅ J) {P Q : D} {N N' : C} {W : E} {V₀ V₁ : V}
    (pG : W ⟶ G.obj P) (pH : V₀ ⟶ H.obj W) (t : V₀ ⟶ V₁)
    (pJ : V₁ ⟶ J.obj Q) (c : Q ⟶ P)
    (a : P ⟶ F.obj N) (b : Q ⟶ F.obj N') (q : N' ⟶ N)
    (ht : pH ≫ H.map pG ≫ e.hom.app P = t ≫ pJ ≫ J.map c)
    (hc : pJ ≫ J.map c ≫ J.map a = pJ ≫ J.map b ≫ J.map (F.map q)) :
    pH ≫ H.map (pG ≫ G.map a) ≫ e.hom.app (F.obj N) =
      t ≫ pJ ≫ J.map b ≫ J.map (F.map q) := by
  have hn := e.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% ht]
  exact congrArg (t ≫ ·) hc

private theorem projection_word_expansions
    {C D : Type*} [Category C] [Category D] {H : C ⥤ D}
    {W W' : C} {V₀ V₁ V₂ V₃ : D}
    {p p' : W ⟶ W'} {q q' : V₁ ⟶ V₂}
    {a : V₀ ⟶ H.obj W} {b : H.obj W' ⟶ V₃}
    {c : V₀ ⟶ V₁} {d : V₂ ⟶ V₃}
    (hp : p = p') (hq : q = q')
    (he : a ≫ H.map p' ≫ b = c ≫ q' ≫ d) :
    a ≫ H.map p ≫ b = c ≫ q ≫ d := by
  rw [hp, hq]
  exact he

private theorem interchange_word_app
    {C D E F G H : Type*} [Category C] [Category D] [Category E]
    [Category F] [Category G] [Category H]
    (J : C ⥤ D) (R : D ⥤ E) (I : E ⥤ F) (Q : F ⥤ G)
    (K : D ⥤ H) (P : H ⥤ F) (U : C ⥤ H) (S : H ⥤ G)
    (α : R ⋙ I ≅ K ⋙ P) (β : P ⋙ Q ≅ S) (γ : U ≅ J ⋙ K) (N : C) :
    (Functor.associator J R (I ⋙ Q) ≪≫
      Functor.isoWhiskerLeft J
        ((Functor.associator R I Q).symm ≪≫
          Functor.isoWhiskerRight α Q ≪≫ Functor.associator K P Q) ≪≫
      (Functor.associator J K (P ⋙ Q)).symm ≪≫
      Functor.isoWhiskerRight γ.symm (P ⋙ Q) ≪≫
      Functor.isoWhiskerLeft U β).hom.app N =
      Q.map (α.hom.app (J.obj N)) ≫ β.hom.app (K.obj (J.obj N)) ≫
        S.map (γ.inv.app N) := by
  have hn := β.hom.naturality (γ.inv.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  exact congrArg (Q.map (α.hom.app (J.obj N)) ≫ ·) hn

private theorem whiskered_interchange_app
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ V) {J : D ⥤ V}
    (e : G ⋙ H ≅ J) (P : C) :
    (Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F e).hom.app P =
      e.hom.app (F.obj P) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]

private theorem iso_then_refl_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (P : C) :
    (e ≪≫ Iso.refl G).hom.app P = e.hom.app P := by
  simp only [Iso.trans_refl]

private theorem interchange_prefix_transport_split
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ V} {J : D ⥤ V}
    (e : G ⋙ H ≅ J) {P Q : D} {N N' N₀ N₀' : C} {W : E} {V₀ V₁ : V}
    (pG : W ⟶ G.obj P) (pH : V₀ ⟶ H.obj W) (t : V₀ ⟶ V₁)
    (pJ : V₁ ⟶ J.obj Q) (c : Q ⟶ P)
    (a : P ⟶ F.obj N₀) (a₂ : N₀ ⟶ N)
    (b : Q ⟶ F.obj N₀') (b₂ : N₀' ⟶ N') (q : N' ⟶ N)
    (ht : pH ≫ H.map pG ≫ e.hom.app P = t ≫ pJ ≫ J.map c)
    (hc : pJ ≫ J.map c ≫ J.map (a ≫ F.map a₂) =
      pJ ≫ J.map (b ≫ F.map b₂) ≫ J.map (F.map q)) :
    pH ≫ H.map (pG ≫ G.map a ≫ G.map (F.map a₂)) ≫ e.hom.app (F.obj N) =
      t ≫ (pJ ≫ J.map b ≫ J.map (F.map b₂)) ≫ (F ⋙ J).map q := by
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
    interchange_prefix_transport e pG pH t pJ c
      (a ≫ F.map a₂) (b ≫ F.map b₂) q ht hc

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A Cartesian proper/open interchange preserves successive projection maps.

Source: Stacks more-etale.tex, Tag 0F7B; sites-cohomology.tex, Tags 0GL1 and
0B56; the open and proper composition normalizations of Tag 0E48.
(auxiliary; not a blueprint node).

Proof: put f0=e r and use the compactifications c=(e,r) and ce=(e k,p).
The Cartesian square supplies a compatible tower over the compactification
(i,q) of g. Apply the existing general tower projection calculation to Ra M
and K. That calculation pastes the proper/open tensor square with the open
projection composition identity and the proper counit composition identity.
Factor the graph-word projection for (a,e,r), and for (a,e k,p q), as the
corresponding compactification projection on Ra M followed by the proper
projection for a and the inverse pullback compositor. Proper-projection naturality
and inverse threefold pullback associativity give these factorizations.
Cancel the identity-direct-image normalization in I; Cartesian normalization
identifies its exchange with the actual proper/open exchange used by the
tower. Naturality of I moves the projection for a past the interchange.
Finally the mixed hom/inverse pullback associativity identity identifies
La(c_f0,g) followed by inverse c_a,f0 with inverse c_a,f0g followed by c_f,g.
Functoriality pastes these equations to give the displayed square. No
projection is inverted and no boundedness or quasi-compactness is used.
-/
theorem sfGraphInterchange_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g)
    (sq : IsPullback d.r d.k d.i d.p)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let I := Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
      (etaleGraphOpenNormalization A d.compactification).symm ≪≫
        etaleGraphDiagramInterchange A d
    sfCompactProjection A d.compactification ((d.sourcePresentation.functor A).obj M) K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          d.compactification).map
          (sfGraphWordProjection A d.sourcePresentation M
            ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)) ≫
        I.hom.app (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
            ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))) =
      ((derivedTensor (ModuleCat.{u + 1} A) Z).map (I.hom.app M)).app K ≫
        sfGraphWordProjection A d.compositePresentation M K ≫
        (d.compositePresentation.functor A).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) := by
  let f₀ := d.e ≫ d.r
  let c : Compactification f₀ := {
    Z := d.V, i := d.e, g := d.r, comm := rfl
    isProper := inferInstance, isOpenImmersion := inferInstance }
  let ce : Compactification (f₀ ≫ d.i) := {
    Z := d.P, i := d.e ≫ d.k, g := d.p
    comm := (Category.assoc d.e d.r d.i).trans
      ((congrArg (d.e ≫ ·) d.square.w.symm).trans (Category.assoc d.e d.k d.p).symm)
    isProper := inferInstance, isOpenImmersion := inferInstance }
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.e).mapDerivedCategory
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d.compactification
  let Ra := (lowerStar (ModuleCat.{u + 1} A) d.a).rightDerivedFunctor
  let E₀ : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙ G ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (d.compactification.comp ce) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (openImmersionLowerShriekLowerStarExchangeIso A sq)
            (lowerStar (ModuleCat.{u + 1} A) d.q).rightDerivedFunctor ≪≫
          Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) d.e d.k).symm _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q)
  have hE₀ (N : DerivedCategoryModule A d.W) :
      E₀.hom.app N =
        (lowerStar (ModuleCat.{u + 1} A) d.q).rightDerivedFunctor.map
          ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq).app (J.obj N)) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.k).mapDerivedCategory.obj (J.obj N)) ≫
        (lowerStar (ModuleCat.{u + 1} A) (d.p ≫ d.q)).rightDerivedFunctor.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).inv.app N) := by
    exact interchange_word_app J
      (lowerStar (ModuleCat.{u + 1} A) d.r).rightDerivedFunctor
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
      (lowerStar (ModuleCat.{u + 1} A) d.q).rightDerivedFunctor
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.k).mapDerivedCategory
      (lowerStar (ModuleCat.{u + 1} A) d.p).rightDerivedFunctor
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (d.e ≫ d.k)).mapDerivedCategory
      (lowerStar (ModuleCat.{u + 1} A) (d.p ≫ d.q)).rightDerivedFunctor
      (openImmersionLowerShriekLowerStarExchangeIso A sq)
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q)
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) d.e d.k) N
  have hcomp : f₀ ≫ g = ce.i ≫ (ce.g ≫ d.compactification.g) := by
    calc
      f₀ ≫ g = (f₀ ≫ d.i) ≫ d.q :=
        (congrArg (f₀ ≫ ·) d.facG.symm).trans (Category.assoc f₀ d.i d.q).symm
      _ = (ce.i ≫ ce.g) ≫ d.q := by rw [← ce.comm]
      _ = _ := Category.assoc ce.i ce.g d.q
  have ht := tower_projection_canonical
    (ModuleCat.{u + 1} A) f₀ g d.compactification ce c d.k sq rfl
    hcomp E₀ (by
      intro N
      have ho :
          (((mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).symm ≪≫
              mapDerivedCategoryOpenImmersionLowerShriekCongr
                (ModuleCat.{u + 1} A) (show c.i ≫ d.k = ce.i from rfl)).hom.app N) =
            (mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) d.e d.k).inv.app N := by
        dsimp only [c, ce]
        delta mapDerivedCategoryOpenImmersionLowerShriekCongr
        change (((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) d.e d.k).symm ≪≫ Iso.refl _).hom.app N) = _
        exact iso_then_refl_app _ N
      exact (hE₀ N).trans (congrArg (fun z ↦
        (lowerStar (ModuleCat.{u + 1} A) d.q).rightDerivedFunctor.map
          ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq).app
            (J.obj N)) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.k).mapDerivedCategory.obj
            (J.obj N)) ≫
        (lowerStar (ModuleCat.{u + 1} A) (d.p ≫ d.q)).rightDerivedFunctor.map z) ho.symm))
    (Ra.obj M) K
  have hf : f = d.a ≫ f₀ := d.facF.symm
  have hh : f ≫ g = d.a ≫ (f₀ ≫ g) :=
    (congrArg (· ≫ g) hf).trans (Category.assoc d.a f₀ g)
  have hs := sfGraphProjectionWord_proper_prefix (ModuleCat.{u + 1} A) c d.a f hf M
    ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)
  have hc := sfGraphProjectionWord_proper_prefix (ModuleCat.{u + 1} A) (d.compactification.comp ce)
    d.a (f ≫ g) hh M K
  change sfGraphWordProjection A d.sourcePresentation M
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) = _ at hs
  change sfGraphWordProjection A d.compositePresentation M K = _ at hc
  have hcoeff := map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) d.a f₀ g f (f₀ ≫ g) (f ≫ g) hf rfl rfl K
  have hnat := properProjection_naturality_right (ModuleCat.{u + 1} A) d.a M _ _
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f₀ g).hom.app K)
  have htransport := coefficient_transport_grouped
    (F := Ra)
    (G := rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (d.compactification.comp ce))
    (T := (derivedTensor (ModuleCat.{u + 1} A) X).obj M)
    (U := (derivedTensor (ModuleCat.{u + 1} A) d.W).obj (Ra.obj M))
    (L := (upperStar (ModuleCat.{u + 1} A) d.a).leftDerivedFunctor) hnat hcoeff
    (((projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (d.compactification.comp ce)).app (Ra.obj M)).app K)
  intro I
  have hI (P : DerivedCategoryModule A X) : I.hom.app P = E₀.hom.app (Ra.obj P) := by
    dsimp only [I]
    rw [show Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
      (etaleGraphOpenNormalization A d.compactification).symm ≪≫
        etaleGraphDiagramInterchange A d = diagramRawInterchange A d by
      simp only [etaleGraphDiagramInterchange, diagramRawInterchange,
        ← Functor.isoWhiskerLeft_symm, Iso.symm_self_id_assoc]]
    have hr : diagramRawInterchange A d =
        Functor.associator Ra
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) G ≪≫
            Functor.isoWhiskerLeft Ra E₀ := by
      dsimp only [diagramRawInterchange, E₀, Ra, J, c, G,
        EtaleGraphInterchangeDiagram.compactification,
        EtaleGraphInterchangeDiagram.sourcePresentation,
        rightDerivedLowerShriekOfCompactification]
      rw [graphCartesianNormalization A d.k d.r d.p d.i sq]
      rfl
    rw [hr]
    exact whiskered_interchange_app Ra
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) G E₀ P
  rw [hI, hI]
  have hp := interchange_prefix_transport_split (F := Ra) E₀
    (sfCompactProjection A c (Ra.obj M)
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))
    (sfCompactProjection A d.compactification
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj (Ra.obj M)) K)
    (((derivedTensor (ModuleCat.{u + 1} A) Z).map (E₀.hom.app (Ra.obj M))).app K)
    (sfCompactProjection A (d.compactification.comp ce) (Ra.obj M) K)
    (((derivedTensor (ModuleCat.{u + 1} A) d.W).obj (Ra.obj M)).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f₀ g).hom.app K))
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) d.a).app M).app
      ((upperStar (ModuleCat.{u + 1} A) f₀).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) d.a f₀ f hf).inv.app
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K)))
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) d.a).app M).app
      ((upperStar (ModuleCat.{u + 1} A) (f₀ ≫ g)).leftDerivedFunctor.obj K))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) d.a (f₀ ≫ g) (f ≫ g) hh).inv.app K))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K))
    ht htransport
  exact projection_word_expansions hs hc hp

end AlgebraicGeometry.Etale
