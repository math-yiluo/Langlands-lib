/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonInterchange
import WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange
import WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Base change of the explicit graph compositor

Source: Stacks Project, Tags 0F7F and 0F7J; the product-graph argument of
`lem-route-exists-right-derived-lower-shriek-comp-iso`
(auxiliary; not a blueprint node).

The compositor is the constructed product-graph isomorphism. The assertion concerns
its compatibility with the specified compactification exchange, rather than the
existence of some compatible isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  sfGraphCompactSupportCompIso
  upperStar lowerStar openImmersionLowerShriek Functor.leftDerivedFunctor
  Functor.mapDerivedCategoryNatIso
  rightDerivedLowerStarComp etaleGraphNormalizedProperOpenExchange
  rightDerivedLowerStarCompOpenImmersionLowerShriekIso
  exactDerivedBaseChangeMap mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
  etaleGraphPresentationExchange

set_option backward.isDefEq.respectTransparency true in
private theorem graphCartesianNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z)
    [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
    (sq : IsPullback r k i p) :
    etaleGraphNormalizedProperOpenExchange A k r p i sq.toCommSq.flip =
      openImmersionLowerShriekLowerStarExchangeIso A sq := by
  apply Iso.ext
  change (etaleGraphNormalizedProperOpenExchange A k r p i sq.toCommSq.flip).hom =
    openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq
  delta etaleGraphNormalizedProperOpenExchange
  have h := Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))
  exact h.2.2.1 k r p i sq

private noncomputable def graphDiagram
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cg : Compactification g) (ch : Compactification (f ≫ g)) :
    EtaleGraphInterchangeDiagram f g := by
  let φ := pullback.fst ch.g cg.g
  let ψ := pullback.snd ch.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ ch.isProper
  let e := pullback.fst φ ch.i
  let σ := pullback.snd φ ch.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w : ch.i ≫ ch.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← ch.comm, Category.assoc, ← cg.comm]
  let a : X ⟶ pullback φ ch.i := pullback.lift (pullback.lift ch.i (f ≫ cg.i) w) (𝟙 X) (by simp [φ])
  have : IsProper (a ≫ σ) := by
    rw [show a ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
    infer_instance
  have : IsProper a := IsProper.of_comp a σ
  have ae : a ≫ e = pullback.lift ch.i (f ≫ cg.i) w := pullback.lift_fst _ _ _
  let k := pullback.fst ψ cg.i
  let r := pullback.snd ψ cg.i
  have : IsProper r := MorphismProperty.pullback_snd _ _ inferInstance
  let u := pullback.fst e k
  let e' := pullback.snd e k
  let ρ : X ⟶ pullback ψ cg.i := pullback.lift (a ≫ e) f (by rw [ae]; simp [ψ])
  let a' : X ⟶ pullback e k := pullback.lift a ρ (by simp [ρ, k])
  have : IsProper (a' ≫ u) := by
    rw [show a' ≫ u = a from pullback.lift_fst _ _ _]
    infer_instance
  have : IsProper a' := IsProper.of_comp a' u
  exact {
    W := pullback e k
    V := pullback ψ cg.i
    P := pullback ch.g cg.g
    T := cg.Z
    a := a'
    e := e'
    r := r
    k := k
    p := ψ
    i := cg.i
    q := cg.g
    facF := by
      simp [a', e', ρ, r]
    facG := cg.comm.symm
    square := (IsPullback.of_hasPullback ψ cg.i).toCommSq }

private theorem graphDiagram_compactification
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cg : Compactification g) (ch : Compactification (f ≫ g)) :
    (graphDiagram f g cg ch).compactification = cg := by
  rfl

set_option backward.isDefEq.respectTransparency true in
private noncomputable def diagramRawInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g) :
    d.sourcePresentation.functor A ⋙
        Rf_!(d.compactification)[ModuleCat.{u + 1} A] ≅
      d.compositePresentation.functor A :=
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((d.e)_!open[ModuleCat.{u + 1} A])
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square)
              R((d.q)_*[ModuleCat.{u + 1} A]) ≪≫
            Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).symm
          (R((d.p)_*[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.isoWhiskerLeft D((d.e ≫ d.k)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q))

private noncomputable def diagramCompIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (ch : Compactification (f ≫ g))
    (d : EtaleGraphInterchangeDiagram f g) :
    Rf_!(ch)[ModuleCat.{u + 1} A] ≅
      Rf_!(cf)[ModuleCat.{u + 1} A] ⋙
        Rf_!(d.compactification)[ModuleCat.{u + 1} A] :=
  etaleGraphComparisonFromOpen A ch d.compositePresentation ≪≫
    (etaleGraphDiagramInterchange A d).symm ≪≫
    Functor.isoWhiskerRight (etaleGraphComparisonFromOpen A cf d.sourcePresentation).symm
      ((EtaleGraphPresentation.ofCompactification d.compactification).functor A) ≪≫
    Functor.isoWhiskerLeft Rf_!(cf)[ModuleCat.{u + 1} A]
      (etaleGraphOpenNormalization A d.compactification)

private theorem diagramCompIso_raw
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (ch : Compactification (f ≫ g))
    (d : EtaleGraphInterchangeDiagram f g) :
    diagramCompIso A cf ch d =
      etaleGraphComparisonFromOpen A ch d.compositePresentation ≪≫
        (diagramRawInterchange A d).symm ≪≫
        Functor.isoWhiskerRight
          (etaleGraphComparisonFromOpen A cf d.sourcePresentation).symm
          Rf_!(d.compactification)[ModuleCat.{u + 1} A] := by
  apply Iso.ext
  ext M
  simp only [diagramCompIso, etaleGraphDiagramInterchange, diagramRawInterchange,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, CategoryTheory.Functor.map_id, Category.assoc,
    Category.id_comp, Category.comp_id]
  erw [(etaleGraphOpenNormalization A d.compactification).hom.naturality]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private noncomputable def graphUnshrunk
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cg : Compactification g) (ch : Compactification (f ≫ g)) :
    EtaleGraphPresentation (f ≫ g) := by
  let φ := pullback.fst ch.g cg.g
  let ψ := pullback.snd ch.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ ch.isProper
  let e := pullback.fst φ ch.i
  let σ := pullback.snd φ ch.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w : ch.i ≫ ch.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← ch.comm, Category.assoc, ← cg.comm]
  let a : X ⟶ pullback φ ch.i :=
    pullback.lift (pullback.lift ch.i (f ≫ cg.i) w) (𝟙 X) (by simp [φ])
  have : IsProper (a ≫ σ) := by
    rw [show a ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
    infer_instance
  have : IsProper a := IsProper.of_comp a σ
  exact {
    U := pullback φ ch.i
    P := pullback ch.g cg.g
    a := a
    e := e
    p := ψ ≫ cg.g
    fac := by simp [a, e, ψ, ← cg.comm] }

private theorem sfComparison_eq_graphComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f) :
    sfGraphCompactificationComparison A c t.p t.e t.a t.fac =
      etaleGraphComparisonFromOpen A c t := by
  rfl

private theorem graphComparisonFromOpen_cocycle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (cf : Compactification f)
    (s t : EtaleGraphPresentation f) :
    etaleGraphComparisonFromOpen A cf s ≪≫ etaleGraphComparison A cf s t =
      etaleGraphComparisonFromOpen A cf t := by
  apply Iso.ext
  simp only [etaleGraphComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

private theorem graphComparisonFromOpen_congr_e
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U P : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : X ⟶ U) (e e' : U ⟶ P) (p : P ⟶ Y)
    [IsProper a] [IsOpenImmersion e] [IsOpenImmersion e'] [IsProper p]
    (w : e = e') (h : a ≫ e ≫ p = f) (h' : a ≫ e' ≫ p = f) :
    etaleGraphComparisonFromOpen A c
        { U := U, P := P, a := a, e := e, p := p, fac := h } ≪≫
      Functor.isoWhiskerLeft R((a)_*[ModuleCat.{u + 1} A])
        (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) w)
          R((p)_*[ModuleCat.{u + 1} A])) =
    etaleGraphComparisonFromOpen A c
      { U := U, P := P, a := a, e := e', p := p, fac := h' } := by
  subst e'
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.refl_hom]
  erw [Category.comp_id]

attribute [local irreducible] etaleGraphComparisonFromOpen
  sfGraphCompactificationComparison

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

set_option backward.isDefEq.respectTransparency true in
private noncomputable def elementaryInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z U : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g)
    (a : X ⟶ U) (v : d.W ⟶ U) (e : U ⟶ d.P)
    [IsProper a] [IsOpenImmersion v] [IsOpenImmersion e]
    (fac : d.a ≫ v = a) (w : v ≫ e = d.e ≫ d.k) :
    R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((d.p ≫ d.q)_*[ModuleCat.{u + 1} A]) ≅
      d.sourcePresentation.functor A ⋙ Rf_!(d.compactification)[ModuleCat.{u + 1} A] :=
  let B := ModuleCat.{u + 1} A
  let eh := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A d.a v a fac
  let ex := etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square
  Functor.isoWhiskerRight eh.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp B v e).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr B w ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekComp B d.e d.k) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
          (rightDerivedLowerStarComp B d.p d.q).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ex.symm _ ≪≫
        Functor.associator _ _ _)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.associator _ _ _

-- Comparing the explicit interchange words requires their full component normalization.
private theorem elementaryInterchange_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z U : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g)
    (a : X ⟶ U) (v : d.W ⟶ U) (e : U ⟶ d.P)
    [IsProper a] [IsOpenImmersion v] [IsOpenImmersion e]
    (fac : d.a ≫ v = a) (w : v ≫ e = d.e ≫ d.k)
    (hf : a ≫ e ≫ (d.p ≫ d.q) = f ≫ g) :
    let H : EtaleGraphPresentation (f ≫ g) :=
      { U := U, P := d.P, a := a, e := e, p := d.p ≫ d.q, fac := hf }
    elementaryInterchange A d a v e fac w =
      etaleGraphShrinkInterchange A H d.a v fac ≪≫
        Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
          (Functor.isoWhiskerRight
            (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) w)
            R((d.p ≫ d.q)_*[ModuleCat.{u + 1} A])) ≪≫
        (diagramRawInterchange A d).symm := by
  dsimp only
  apply Iso.ext
  ext M
  have hn := (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q).inv.naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
      d.e d.k).hom.app (R((d.a)_*[ModuleCat.{u + 1} A]).obj M))
  simp only [elementaryInterchange, diagramRawInterchange, etaleGraphShrinkInterchange,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Category.assoc,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  simp only [← Category.assoc]
  exact (Category.comp_id _).trans (Category.comp_id _)

attribute [local semireducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

private theorem graphCompositor_elementary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) :
    let H := graphUnshrunk f g cg ch
    let d := graphDiagram f g cg ch
    let v := pullback.fst H.e d.k
    let fac : d.a ≫ v = H.a := by
      dsimp [d, H, v, graphDiagram, graphUnshrunk]
      simp
    sfGraphCompactSupportCompIso A f g cf cg ch =
      etaleGraphComparisonFromOpen A ch H ≪≫
        elementaryInterchange A d H.a v H.e fac pullback.condition ≪≫
        Functor.isoWhiskerRight
          (etaleGraphComparisonFromOpen A cf d.sourcePresentation).symm
          Rf_!(d.compactification)[ModuleCat.{u + 1} A] := by
  dsimp only
  rw [← sfComparison_eq_graphComparison A ch (graphUnshrunk f g cg ch),
    ← sfComparison_eq_graphComparison A cf (graphDiagram f g cg ch).sourcePresentation]
  unfold sfGraphCompactSupportCompIso elementaryInterchange
  rw [graphCartesianNormalization A
    (graphDiagram f g cg ch).k (graphDiagram f g cg ch).r
    (graphDiagram f g cg ch).p (graphDiagram f g cg ch).i
    (IsPullback.of_hasPullback (graphDiagram f g cg ch).p
      (graphDiagram f g cg ch).i).flip]
  rfl

private theorem graphCompositor_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g)) :
    sfGraphCompactSupportCompIso A f g cf cg ch =
      diagramCompIso A cf ch (graphDiagram f g cg ch) := by
  let H := graphUnshrunk f g cg ch
  let d := graphDiagram f g cg ch
  let v := pullback.fst H.e d.k
  have fac : d.a ≫ v = H.a := by
    dsimp [d, H, v, graphDiagram, graphUnshrunk]
    simp
  have hs := (etaleGraphComparisonInterchange A).1 ch H d.a v fac
  have hsIso : etaleGraphComparison A ch H (H.shrink d.a v fac) =
      etaleGraphShrinkInterchange A H d.a v fac := Iso.ext hs
  have hcongr := graphComparisonFromOpen_congr_e A ch d.a (v ≫ H.e)
    (d.e ≫ d.k) (d.p ≫ d.q) pullback.condition
    (H.shrink d.a v fac).fac d.compositePresentation.fac
  have hc := graphComparisonFromOpen_cocycle A ch H (H.shrink d.a v fac)
  rw [hsIso] at hc
  change etaleGraphComparisonFromOpen A ch (H.shrink d.a v fac) ≪≫
      Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
        (Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            pullback.condition) R((d.p ≫ d.q)_*[ModuleCat.{u + 1} A])) =
      etaleGraphComparisonFromOpen A ch d.compositePresentation at hcongr
  have hb : etaleGraphComparisonFromOpen A ch H ≪≫
      etaleGraphShrinkInterchange A H d.a v fac ≪≫
        Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
          (Functor.isoWhiskerRight
            (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
              pullback.condition) R((d.p ≫ d.q)_*[ModuleCat.{u + 1} A])) =
      etaleGraphComparisonFromOpen A ch d.compositePresentation := by
    rw [← Iso.trans_assoc, hc]
    exact hcongr
  rw [graphCompositor_elementary, diagramCompIso_raw,
    elementaryInterchange_normalization A d H.a v H.e fac pullback.condition H.fac]
  have hh := congrArg (fun z ↦ z ≪≫ (diagramRawInterchange A d).symm ≪≫
    Functor.isoWhiskerRight
      (etaleGraphComparisonFromOpen A cf d.sourcePresentation).symm
      Rf_!(d.compactification)[ModuleCat.{u + 1} A]) hb
  simpa only [d, H, graphDiagram_compactification, graphUnshrunk, graphDiagram,
    Iso.trans_assoc] using hh

private theorem compare_diagram_compositors
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F₁ F₂ : C ⥤ D} {G₁ G₂ G₁' G₂' : D ⥤ E} {H H₁ H₂ : C ⥤ E}
    (x₁ : F ≅ F₁) (x₂ : F ≅ F₂) (y₁ : G₁ ≅ G₁') (y₂ : G₂ ≅ G₂')
    (z₁ : H ≅ H₁) (z₂ : H ≅ H₂) (t : G₁ ≅ G₂)
    (I₁ : F₁ ⋙ G₁ ≅ H₁) (I₂ : F₂ ⋙ G₂ ≅ H₂)
    (hi : I₁.hom ≫ (z₁.symm ≪≫ z₂).hom =
      Functor.whiskerRight (x₁.symm ≪≫ x₂).hom G₁ ≫
        Functor.whiskerLeft F₂ t.hom ≫ I₂.hom) :
    (z₁ ≪≫ I₁.symm ≪≫ Functor.isoWhiskerRight x₁.symm G₁ ≪≫
      Functor.isoWhiskerLeft F y₁).hom ≫
        Functor.whiskerLeft F (y₁.symm ≪≫ t ≪≫ y₂).hom =
    (z₂ ≪≫ I₂.symm ≪≫ Functor.isoWhiskerRight x₂.symm G₂ ≪≫
      Functor.isoWhiskerLeft F y₂).hom := by
  ext M
  have h := congr_app hi M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc] at h
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  apply (cancel_mono (y₂.inv.app _)).1
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (cancel_mono (G₂.map (x₂.hom.app M))).1
  simp only [Category.assoc, Category.id_comp, Category.comp_id,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [← t.hom.naturality]
  apply (cancel_mono (I₂.hom.app M)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  simp [← Functor.map_comp, ← Category.assoc]

attribute [local irreducible] graphDiagram graphUnshrunk

private theorem compactification_graphComparison_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c s t : Compactification f) :
    (etaleGraphOpenNormalization A s).symm ≪≫
      etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification s)
        (EtaleGraphPresentation.ofCompactification t) ≪≫
      etaleGraphOpenNormalization A t =
      rightDerivedLowerShriekOfCompactificationIso A s t := by
  rw [(etaleGraphComparisonBaseChange A c).2.2.2.2.2.2 s t]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem graphComparison_change_compactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c c' : Compactification f) (t : EtaleGraphPresentation f) :
    rightDerivedLowerShriekOfCompactificationIso A c c' ≪≫
      etaleGraphComparisonFromOpen A c' t = etaleGraphComparisonFromOpen A c t := by
  have h := (etaleGraphComparisonBaseChange A c).2.1 c' t
  have hn := (etaleGraphComparisonBaseChange A c).2.2.2.2.2.2 c c'
  have hc := (etaleGraphComparisonBaseChange A c).2.2.2.1
    (EtaleGraphPresentation.ofCompactification c)
    (EtaleGraphPresentation.ofCompactification c') t
  rw [(etaleGraphComparisonBaseChange A c).2.1 c t, h, hn] at hc
  apply Iso.ext
  have he := congrArg Iso.hom hc
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] at he
  apply (cancel_epi (etaleGraphOpenNormalization A c).hom).1
  simpa only [Iso.trans_hom] using he

private theorem transported_compositor_baseChange
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {F F₁ : C ⥤ D} {G G₁ : D ⥤ E} {H H₁ : C ⥤ E}
    {F' F₁' : C' ⥤ D'} {G' G₁' : D' ⥤ E'} {H' H₁' : C' ⥤ E'}
    (U : C ⥤ C') (V : D ⥤ D') (W : E ⥤ E')
    (x : F ≅ F₁) (y : G ≅ G₁) (z : H ≅ H₁)
    (x' : F' ≅ F₁') (y' : G' ≅ G₁') (z' : H' ≅ H₁')
    (I : F₁ ⋙ G₁ ≅ H₁) (I' : F₁' ⋙ G₁' ≅ H₁')
    (ef : F ⋙ V ⟶ U ⋙ F') (eg : G ⋙ W ⟶ V ⋙ G')
    (eh : H ⋙ W ⟶ U ⋙ H')
    (ef₁ : F₁ ⋙ V ⟶ U ⋙ F₁') (eg₁ : G₁ ⋙ W ⟶ V ⋙ G₁')
    (eh₁ : H₁ ⋙ W ⟶ U ⋙ H₁')
    (hx : ∀ M, V.map (x.hom.app M) ≫ ef₁.app M =
      ef.app M ≫ x'.hom.app (U.obj M))
    (hy : ∀ N, W.map (y.hom.app N) ≫ eg₁.app N =
      eg.app N ≫ y'.hom.app (V.obj N))
    (hz : ∀ M, W.map (z.hom.app M) ≫ eh₁.app M =
      eh.app M ≫ z'.hom.app (U.obj M))
    (hI : ∀ M, W.map (I.hom.app M) ≫ eh₁.app M =
      eg₁.app (F₁.obj M) ≫ G₁'.map (ef₁.app M) ≫ I'.hom.app (U.obj M))
    (M : C) :
    W.map (z.hom.app M ≫ I.inv.app M ≫ G₁.map (x.inv.app M) ≫ y.inv.app (F.obj M)) ≫
      eg.app (F.obj M) ≫ G'.map (ef.app M) =
    eh.app M ≫ z'.hom.app (U.obj M) ≫ I'.inv.app (U.obj M) ≫
      G₁'.map (x'.inv.app (U.obj M)) ≫ y'.inv.app (F'.obj (U.obj M)) := by
  have hyi : W.map (y.inv.app (F.obj M)) ≫ eg.app (F.obj M) =
      eg₁.app (F.obj M) ≫ y'.inv.app (V.obj (F.obj M)) := by
    apply (cancel_epi (W.map (y.hom.app (F.obj M)))).1
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc]
    rw [reassoc_of% hy]
    simp only [W.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  have hxi : V.map (x.inv.app M) ≫ ef.app M =
      ef₁.app M ≫ x'.inv.app (U.obj M) := by
    apply (cancel_epi (V.map (x.hom.app M))).1
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc]
    rw [reassoc_of% hx]
    simp only [V.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hyi]
  rw [← y'.inv.naturality]
  have hn := eg₁.naturality (x.inv.app M)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← G₁'.map_comp_assoc, hxi, G₁'.map_comp]
  dsimp only [Functor.comp_obj]
  apply (cancel_mono (y'.hom.app (F'.obj (U.obj M)))).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_mono (G₁'.map (x'.hom.app (U.obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  apply (cancel_mono (I'.hom.app (U.obj M))).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Category.id_comp,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [← hI]
  simp only [← W.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, G₁'.map_id, Category.id_comp]
  exact hz M

private theorem diagramCompIso_independent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (ch : Compactification (f ≫ g))
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) :
    (diagramCompIso A cf ch d₁).hom ≫
        Functor.whiskerLeft Rf_!(cf)[ModuleCat.{u + 1} A]
          ((etaleGraphOpenNormalization A d₁.compactification).symm ≪≫
            etaleGraphComparison A d₁.compactification
              (EtaleGraphPresentation.ofCompactification d₁.compactification)
              (EtaleGraphPresentation.ofCompactification d₂.compactification) ≪≫
            etaleGraphOpenNormalization A d₂.compactification).hom =
      (diagramCompIso A cf ch d₂).hom := by
  have hi := (etaleGraphComparisonInterchange A).2 cf ch d₁ d₂
  exact compare_diagram_compositors
    (etaleGraphComparisonFromOpen A cf d₁.sourcePresentation)
    (etaleGraphComparisonFromOpen A cf d₂.sourcePresentation)
    (etaleGraphOpenNormalization A d₁.compactification)
    (etaleGraphOpenNormalization A d₂.compactification)
    (etaleGraphComparisonFromOpen A ch d₁.compositePresentation)
    (etaleGraphComparisonFromOpen A ch d₂.compositePresentation)
    (etaleGraphComparison A d₁.compactification
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification))
    (etaleGraphDiagramInterchange A d₁) (etaleGraphDiagramInterchange A d₂) hi

private structure DiagramPullback
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (d : EtaleGraphInterchangeDiagram f g)
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z) where
  diagram : EtaleGraphInterchangeDiagram f' g'
  w : diagram.W ⟶ d.W
  v : diagram.V ⟶ d.V
  p : diagram.P ⟶ d.P
  t : diagram.T ⟶ d.T
  aSquare : IsPullback a diagram.a d.a w
  eSquare : IsPullback w diagram.e d.e v
  rSquare : IsPullback v diagram.r d.r b
  kSquare : IsPullback v diagram.k d.k p
  pSquare : IsPullback p diagram.p d.p t
  iSquare : IsPullback b diagram.i d.i t
  qSquare : IsPullback t diagram.q d.q c

private noncomputable def diagramPullback
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g)
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) :
    DiagramPullback (f' := f') (g' := g') d a b c := by
  let cg := d.compactification.ofIsPullback sqg
  let t := pullback.fst d.q c
  let p := pullback.fst d.p t
  let pp := pullback.snd d.p t
  let v := pullback.fst d.r b
  let rr := pullback.snd d.r b
  have hi : IsPullback b cg.i d.i t := d.compactification.isPullback_i_ofIsPullback sqg
  have hr : IsPullback v rr d.r b := .of_hasPullback d.r b
  let kk : pullback d.r b ⟶ pullback d.p t :=
    pullback.lift (v ≫ d.k) (rr ≫ cg.i) (by
      calc
        (v ≫ d.k) ≫ d.p = (v ≫ d.r) ≫ d.i := by
          rw [Category.assoc, d.square.w, Category.assoc]
        _ = (rr ≫ b) ≫ d.i := by rw [hr.w]
        _ = (rr ≫ cg.i) ≫ t := by rw [Category.assoc, hi.w, Category.assoc])
  have hp : IsPullback p pp d.p t := .of_hasPullback d.p t
  have hk : IsPullback v kk d.k p := by
    apply IsPullback.of_bot _ (by simp [kk, p]) hp
    simpa only [kk, pp, pullback.lift_snd, d.square.w] using hr.paste_vert hi
  have : IsOpenImmersion kk :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hk inferInstance
  let w := pullback.fst d.e v
  let ee := pullback.snd d.e v
  let liftV : X' ⟶ pullback d.r b := pullback.lift (a ≫ d.a ≫ d.e) f' (by
    rw [Category.assoc, Category.assoc, d.facF, sqf.w])
  let aa : X' ⟶ pullback d.e v := pullback.lift (a ≫ d.a) liftV (by simp [liftV, v])
  have he : IsPullback w ee d.e v := .of_hasPullback d.e v
  have ha : IsPullback a aa d.a w := by
    apply IsPullback.of_bot _ (by simp [aa, w]) (he.paste_vert hr)
    simpa only [aa, ee, liftV, rr, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.assoc, d.facF] using sqf
  have : IsProper aa :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ha inferInstance
  let dd : EtaleGraphInterchangeDiagram f' g' := {
    W := pullback d.e v
    V := pullback d.r b
    P := pullback d.p t
    T := cg.Z
    a := aa
    e := ee
    r := rr
    k := kk
    p := pp
    i := cg.i
    q := cg.g
    facF := by simp [aa, ee, liftV, rr]
    facG := cg.comm.symm
    square := ⟨by simp [kk, pp]⟩ }
  exact {
    diagram := dd
    w := w
    v := v
    p := p
    t := t
    aSquare := ha
    eSquare := he
    rSquare := hr
    kSquare := hk
    pSquare := hp
    iSquare := hi
    qSquare := .of_hasPullback d.q c }

private def DiagramPullback.sourceBaseChange
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {d : EtaleGraphInterchangeDiagram f g}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    (D : DiagramPullback (f' := f') (g' := g') d a b c) :
    d.sourcePresentation.BaseChange D.diagram.sourcePresentation a b where
  u := D.w
  w := D.v
  aSquare := D.aSquare
  eSquare := D.eSquare
  pSquare := D.rSquare

private def DiagramPullback.compositeBaseChange
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {d : EtaleGraphInterchangeDiagram f g}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    (D : DiagramPullback (f' := f') (g' := g') d a b c) :
    d.compositePresentation.BaseChange D.diagram.compositePresentation a c where
  u := D.w
  w := D.p
  aSquare := D.aSquare
  eSquare := D.eSquare.paste_vert D.kSquare
  pSquare := D.pSquare.paste_vert D.qSquare

set_option backward.isDefEq.respectTransparency true in
private theorem graphInterchangeCube
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {d : EtaleGraphInterchangeDiagram f g}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    (D : DiagramPullback (f' := f') (g' := g') d a b c) :
    Functor.whiskerRight
        (etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square).hom
        D((D.t)^*[ModuleCat.{u + 1} A]) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft D((d.k)_!open[ModuleCat.{u + 1} A])
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) D.pSquare.toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) D.kSquare).inv
        R((D.diagram.p)_*[ModuleCat.{u + 1} A]) ≫
      (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft R((d.r)_*[ModuleCat.{u + 1} A])
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) D.iSquare).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) D.rSquare.toCommSq)
        D((D.diagram.i)_!open[ModuleCat.{u + 1} A]) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft D((D.v)^*[ModuleCat.{u + 1} A])
        (etaleGraphNormalizedProperOpenExchange A D.diagram.k D.diagram.r
          D.diagram.p D.diagram.i D.diagram.square).hom := by
  delta etaleGraphNormalizedProperOpenExchange
  have h := Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))
  exact h.2.2.2.2.2.2.2
      d.k d.r d.p d.i D.diagram.k D.diagram.r D.diagram.p D.diagram.i
      D.v D.p b D.t d.square D.diagram.square
      D.kSquare D.iSquare D.pSquare D.rSquare

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

set_option backward.isDefEq.respectTransparency true in
private noncomputable def compactificationExactExchange
    (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y}
    (cf : Compactification f) (cf' : Compactification f') (p : cf'.Z ⟶ cf.Z)
    (hi : IsPullback v cf'.i cf.i p) (hp : IsPullback p cf'.g cf.g b) :
    Rf_!(cf)[ModuleCat.{u + 1} A] ⋙ D((b)^*[ModuleCat.{u + 1} A]) ⟶
      D((v)^*[ModuleCat.{u + 1} A]) ⋙ Rf_!(cf')[ModuleCat.{u + 1} A] :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D((cf.i)_!open[ModuleCat.{u + 1} A])
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) hp.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) hi).inv R((cf'.g)_*[ModuleCat.{u + 1} A])

attribute [local semireducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

private theorem compactificationExactExchange_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y}
    (cf : Compactification f) (sq : IsPullback v f' f b) :
    compactificationExactExchange A cf (cf.ofIsPullback sq)
        (pullback.fst cf.g b) (cf.isPullback_i_ofIsPullback sq)
        (cf.isPullback_g_ofIsPullback sq).flip =
      Functor.whiskerLeft Rf_!(cf)[ModuleCat.{u + 1} A]
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) b).inv ≫
        rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq cf ≫
        Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).hom
          Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} A] := by
  ext M
  have h := congr_app (exact_exchange_transport A
    (IsPullback.of_hasPullback cf.g b).toCommSq)
      (D((cf.i)_!open[ModuleCat.{u + 1} A]).obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simp only [compactificationExactExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  rw [← h]
  dsimp only [rightDerivedLowerShriekOfCompactification, Functor.comp_map,
    Compactification.ofIsPullback, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private def compactificationPresentationBaseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y}
    (cf : Compactification f) (cf' : Compactification f') (p : cf'.Z ⟶ cf.Z)
    (hi : IsPullback v cf'.i cf.i p) (hp : IsPullback p cf'.g cf.g b) :
    (EtaleGraphPresentation.ofCompactification cf).BaseChange
      (EtaleGraphPresentation.ofCompactification cf') v b where
  u := v
  w := p
  aSquare := by
    change IsPullback v (𝟙 X') (𝟙 X) v
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  eSquare := hi
  pSquare := hp

private theorem graphOpenNormalization_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y}
    (cf : Compactification f) (cf' : Compactification f') (p : cf'.Z ⟶ cf.Z)
    (hi : IsPullback v cf'.i cf.i p) (hp : IsPullback p cf'.g cf.g b)
    (M : DerivedCategoryModule A X) :
    D((b)^*[ModuleCat.{u + 1} A]).map
        ((etaleGraphOpenNormalization A cf).hom.app M) ≫
      (compactificationExactExchange A cf cf' p hi hp).app M =
    (etaleGraphPresentationExchange A
        (compactificationPresentationBaseChange cf cf' p hi hp)).app M ≫
      (etaleGraphOpenNormalization A cf').hom.app
        (D((v)^*[ModuleCat.{u + 1} A]).obj M) := by
  have hid := sfExactExchangePasting.1 A v M
  have hn := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) hp.toCommSq).naturality
    (D((cf.i)_!open[ModuleCat.{u + 1} A]).map
      ((rightDerivedLowerStarIdIso A X).hom.app M))
  have ho := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} A) hi).inv.naturality
      ((rightDerivedLowerStarIdIso A X).hom.app M)
  simp only [etaleGraphOpenNormalization, compactificationExactExchange,
    etaleGraphPresentationExchange, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.assoc, Category.id_comp, Category.comp_id]
  dsimp only [Functor.comp_map, Functor.id_obj] at hn ho
  dsimp only [EtaleGraphPresentation.ofCompactification, EtaleGraphPresentation.functor,
    compactificationPresentationBaseChange, Functor.comp_map, Functor.comp_obj]
  erw [D((b)^*[ModuleCat.{u + 1} A]).map_id]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  erw [reassoc_of% hn]
  have hmo := congrArg (R((cf'.g)_*[ModuleCat.{u + 1} A]).map) ho
  simp only [Functor.map_comp] at hmo
  erw [hmo]
  erw [hid]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [EtaleGraphPresentation.functor, Functor.comp_obj]
  erw [Category.comp_id]

attribute [local irreducible] diagramRawInterchange compactificationExactExchange

private theorem paste_word
    {C : Type*} [Category C]
    {A B D E F G H I J K L N O P Q S : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (e : F ⟶ G) (f : G ⟶ H) (t : H ⟶ I)
    (c₁ : D ⟶ J) (d₁ : J ⟶ F) (e₁ : J ⟶ K)
    (h : K ⟶ L) (o₁ : L ⟶ G)
    (j : B ⟶ N) (r : N ⟶ O) (γ : O ⟶ K)
    (s₁ : O ⟶ S) (s₂ : S ⟶ P) (v : P ⟶ Q) (k : L ⟶ Q) (o : Q ⟶ H)
    (hp : c ≫ d = c₁ ≫ d₁)
    (ho : d₁ ≫ e = e₁ ≫ h ≫ o₁)
    (hc : b ≫ c₁ ≫ e₁ = j ≫ r ≫ γ)
    (hn : o₁ ≫ f = k ≫ o)
    (hg : s₁ ≫ s₂ ≫ v = γ ≫ h ≫ k) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ t = a ≫ j ≫ r ≫ s₁ ≫ s₂ ≫ v ≫ o ≫ t := by
  rw [reassoc_of% hp, reassoc_of% ho, reassoc_of% hc,
    reassoc_of% hn, ← reassoc_of% hg]

-- The component calculation instantiates five derived exchange identities.
private theorem diagramRawInterchange_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {d : EtaleGraphInterchangeDiagram f g}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    (D : DiagramPullback (f' := f') (g' := g') d a b c)
    (M : DerivedCategoryModule A X) :
    D((c)^*[ModuleCat.{u + 1} A]).map
        ((diagramRawInterchange A d).hom.app M) ≫
      (etaleGraphPresentationExchange A D.compositeBaseChange).app M =
    (compactificationExactExchange A d.compactification D.diagram.compactification
        D.t D.iSquare D.qSquare).app ((d.sourcePresentation.functor A).obj M) ≫
      Rf_!(D.diagram.compactification)[ModuleCat.{u + 1} A].map
        ((etaleGraphPresentationExchange A D.sourceBaseChange).app M) ≫
      (diagramRawInterchange A D.diagram).hom.app
        (D((a)^*[ModuleCat.{u + 1} A]).obj M) := by
  let B := ModuleCat.{u + 1} A
  let K := R((d.a)_*[B]).obj M
  have hp := sfExactExchangePasting.2.1 A D.pSquare.toCommSq D.qSquare.toCommSq
    (D((d.e ≫ d.k)_!open[B]).obj K)
  have ho := sfExactExchangePasting.2.2 A D.eSquare D.kSquare K
  have hc := congr_app (graphInterchangeCube A D) (D((d.e)_!open[B]).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at hc
  have nq₁ := (exactDerivedBaseChangeMap B D.qSquare.toCommSq).naturality
    (R((d.p)_*[B]).map
      ((mapDerivedCategoryOpenImmersionLowerShriekComp B d.e d.k).inv.app K))
  have nq₂ := (exactDerivedBaseChangeMap B D.qSquare.toCommSq).naturality
    ((etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square).hom.app
      (D((d.e)_!open[B]).obj K))
  have np := (exactDerivedBaseChangeMap B D.pSquare.toCommSq).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekComp B d.e d.k).inv.app K)
  let ξ := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B D.eSquare).inv.app K ≫
    D((D.diagram.e)_!open[B]).map
      ((exactDerivedBaseChangeMap B D.aSquare.toCommSq).app M)
  have ng := (etaleGraphNormalizedProperOpenExchange A D.diagram.k D.diagram.r
    D.diagram.p D.diagram.i D.diagram.square).hom.naturality ξ
  have no := (mapDerivedCategoryOpenImmersionLowerShriekComp B
    D.diagram.e D.diagram.k).inv.naturality
      ((exactDerivedBaseChangeMap B D.aSquare.toCommSq).app M)
  let ζ := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B
    (D.eSquare.paste_vert D.kSquare)).inv.app K ≫
    D((D.diagram.e ≫ D.diagram.k)_!open[B]).map
      ((exactDerivedBaseChangeMap B D.aSquare.toCommSq).app M)
  have nc := (rightDerivedLowerStarComp B D.diagram.p D.diagram.q).hom.naturality ζ
  simp only [ζ, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc] at nq₁ nq₂ np ng no nc
  delta diagramRawInterchange etaleGraphPresentationExchange compactificationExactExchange
  dsimp only [EtaleGraphInterchangeDiagram.sourcePresentation,
    EtaleGraphInterchangeDiagram.compositePresentation, EtaleGraphPresentation.functor,
    DiagramPullback.sourceBaseChange, DiagramPullback.compositeBaseChange,
    EtaleGraphInterchangeDiagram.compactification, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [reassoc_of% hp]
  rw [← nc]
  rw [reassoc_of% nq₁]
  conv_lhs => rw [reassoc_of% nq₂]
  have hnp := congrArg (R((D.diagram.q)_*[B]).map) np
  have hho := congrArg (fun z ↦ R((D.diagram.q)_*[B]).map
    (R((D.diagram.p)_*[B]).map z)) ho
  have hhc := congrArg (R((D.diagram.q)_*[B]).map) hc
  have hno := congrArg (fun z ↦ R((D.diagram.q)_*[B]).map
    (R((D.diagram.p)_*[B]).map z)) no
  have hng := congrArg (R((D.diagram.q)_*[B]).map) ng
  simp only [ξ, Functor.map_comp, Functor.comp_map, Category.assoc] at hnp hho hhc hno hng
  exact paste_word _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hnp hho hhc hno.symm hng

private theorem graphComparisonFromOpen_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y}
    (cf : Compactification f) (sq : IsPullback v f' f b)
    (t : EtaleGraphPresentation f) (t' : EtaleGraphPresentation f')
    (dt : t.BaseChange t' v b) (M : DerivedCategoryModule A X) :
    D((b)^*[ModuleCat.{u + 1} A]).map
        ((etaleGraphComparisonFromOpen A cf t).hom.app M) ≫
      (etaleGraphPresentationExchange A dt).app M =
    (compactificationExactExchange A cf (cf.ofIsPullback sq)
        (pullback.fst cf.g b) (cf.isPullback_i_ofIsPullback sq)
        (cf.isPullback_g_ofIsPullback sq).flip).app M ≫
      (etaleGraphComparisonFromOpen A (cf.ofIsPullback sq) t').hom.app
        (D((v)^*[ModuleCat.{u + 1} A]).obj M) := by
  have hc := etaleGraphFromOpen_baseChange A cf v b sq t t' dt
  have h := congr_app hc M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc] at h
  have hn := graphOpenNormalization_exchange A cf (cf.ofIsPullback sq)
    (pullback.fst cf.g b) (cf.isPullback_i_ofIsPullback sq)
    (cf.isPullback_g_ofIsPullback sq).flip M
  apply (cancel_epi (D((b)^*[ModuleCat.{u + 1} A]).map
    ((etaleGraphOpenNormalization A cf).hom.app M))).1
  rw [h]
  exact (reassoc_of% hn.symm) _

private noncomputable def chosenCompactificationExactExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} [QuasiCompact f']
    (cf : Compactification f) (cf' : Compactification f')
    (sq : IsPullback v f' f b) :
    Rf_!(cf)[ModuleCat.{u + 1} A] ⋙ D((b)^*[ModuleCat.{u + 1} A]) ⟶
      D((v)^*[ModuleCat.{u + 1} A]) ⋙ Rf_!(cf')[ModuleCat.{u + 1} A] :=
  compactificationExactExchange A cf (cf.ofIsPullback sq)
      (pullback.fst cf.g b) (cf.isPullback_i_ofIsPullback sq)
      (cf.isPullback_g_ofIsPullback sq).flip ≫
    Functor.whiskerLeft D((v)^*[ModuleCat.{u + 1} A])
      (rightDerivedLowerShriekOfCompactificationIso A (cf.ofIsPullback sq) cf').hom

private theorem graphComparisonFromOpen_chosen_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} [QuasiCompact f']
    (cf : Compactification f) (cf' : Compactification f')
    (sq : IsPullback v f' f b)
    (t : EtaleGraphPresentation f) (t' : EtaleGraphPresentation f')
    (dt : t.BaseChange t' v b) (M : DerivedCategoryModule A X) :
    D((b)^*[ModuleCat.{u + 1} A]).map
        ((etaleGraphComparisonFromOpen A cf t).hom.app M) ≫
      (etaleGraphPresentationExchange A dt).app M =
    (chosenCompactificationExactExchange A cf cf' sq).app M ≫
      (etaleGraphComparisonFromOpen A cf' t').hom.app
        (D((v)^*[ModuleCat.{u + 1} A]).obj M) := by
  rw [graphComparisonFromOpen_exchange A cf sq t t' dt M]
  simp only [chosenCompactificationExactExchange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  have h := congr_app (congrArg Iso.hom
    (graphComparison_change_compactification A (cf.ofIsPullback sq) cf' t'))
      (D((v)^*[ModuleCat.{u + 1} A]).obj M)
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  rw [h]

private theorem diagram_chosenExact_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    (cf : Compactification f) (ch : Compactification (f ≫ g))
    (cf' : Compactification f') (ch' : Compactification (f' ≫ g'))
    (d : EtaleGraphInterchangeDiagram f g)
    (d' : EtaleGraphInterchangeDiagram f' g')
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c)
    (sqh : IsPullback a (f' ≫ g') (f ≫ g) c)
    (M : DerivedCategoryModule A X) :
    D((c)^*[ModuleCat.{u + 1} A]).map
        ((diagramCompIso A cf ch d).hom.app M) ≫
      (chosenCompactificationExactExchange A d.compactification d'.compactification sqg).app
        (Rf_!(cf)[ModuleCat.{u + 1} A].obj M) ≫
      Rf_!(d'.compactification)[ModuleCat.{u + 1} A].map
        ((chosenCompactificationExactExchange A cf cf' sqf).app M) =
    (chosenCompactificationExactExchange A ch ch' sqh).app M ≫
      (diagramCompIso A cf' ch' d').hom.app
        (D((a)^*[ModuleCat.{u + 1} A]).obj M) := by
  let D := diagramPullback d sqf sqg
  let κ := rightDerivedLowerShriekOfCompactificationIso A
    D.diagram.compactification d'.compactification
  have ht := transported_compositor_baseChange
    D((a)^*[ModuleCat.{u + 1} A]) D((b)^*[ModuleCat.{u + 1} A])
    D((c)^*[ModuleCat.{u + 1} A])
    (etaleGraphComparisonFromOpen A cf d.sourcePresentation)
    (Iso.refl Rf_!(d.compactification)[ModuleCat.{u + 1} A])
    (etaleGraphComparisonFromOpen A ch d.compositePresentation)
    (etaleGraphComparisonFromOpen A cf' D.diagram.sourcePresentation)
    κ.symm (etaleGraphComparisonFromOpen A ch' D.diagram.compositePresentation)
    (diagramRawInterchange A d) (diagramRawInterchange A D.diagram)
    (chosenCompactificationExactExchange A cf cf' sqf)
    (chosenCompactificationExactExchange A d.compactification d'.compactification sqg)
    (chosenCompactificationExactExchange A ch ch' sqh)
    (etaleGraphPresentationExchange A D.sourceBaseChange)
    (compactificationExactExchange A d.compactification D.diagram.compactification
      D.t D.iSquare D.qSquare)
    (etaleGraphPresentationExchange A D.compositeBaseChange)
    (graphComparisonFromOpen_chosen_exchange A cf cf' sqf
      d.sourcePresentation D.diagram.sourcePresentation D.sourceBaseChange)
    (fun N ↦ by
      simp only [Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
        chosenCompactificationExactExchange, NatTrans.comp_app,
        Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
      change _ = _ ≫ (rightDerivedLowerShriekOfCompactificationIso A
        (d.compactification.ofIsPullback sqg) d'.compactification).hom.app _ ≫
        (rightDerivedLowerShriekOfCompactificationIso A
          (d.compactification.ofIsPullback sqg) d'.compactification).inv.app _
      rw [Iso.hom_inv_id_app, Category.comp_id]
      rfl)
    (graphComparisonFromOpen_chosen_exchange A ch ch' sqh
      d.compositePresentation D.diagram.compositePresentation D.compositeBaseChange)
    (diagramRawInterchange_baseChange A D) M
  have hi := congr_app (diagramCompIso_independent A cf' ch' D.diagram d')
    (D((a)^*[ModuleCat.{u + 1} A]).obj M)
  rw [compactification_graphComparison_normalization] at hi
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hi
  rw [← hi]
  simp only [diagramCompIso_raw, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] at hi ⊢
  simp only [Iso.refl_inv, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc, Iso.symm_inv, κ, Functor.map_comp] at ht
  exact ht

attribute [local semireducible] graphDiagram

private theorem graph_chosenExact_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (f ≫ g))
    (cf' : Compactification f') (cg' : Compactification g')
    (ch' : Compactification (f' ≫ g'))
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c)
    (sqh : IsPullback a (f' ≫ g') (f ≫ g) c)
    (M : DerivedCategoryModule A X) :
    D((c)^*[ModuleCat.{u + 1} A]).map
        ((sfGraphCompactSupportCompIso A f g cf cg ch).hom.app M) ≫
      (chosenCompactificationExactExchange A cg cg' sqg).app
        (Rf_!(cf)[ModuleCat.{u + 1} A].obj M) ≫
      Rf_!(cg')[ModuleCat.{u + 1} A].map
        ((chosenCompactificationExactExchange A cf cf' sqf).app M) =
    (chosenCompactificationExactExchange A ch ch' sqh).app M ≫
      (sfGraphCompactSupportCompIso A f' g' cf' cg' ch').hom.app
        (D((a)^*[ModuleCat.{u + 1} A]).obj M) := by
  rw [graphCompositor_normalization A f g cf cg ch,
    graphCompositor_normalization A f' g' cf' cg' ch']
  have ht := diagram_chosenExact_comp A cf ch cf' ch'
    (graphDiagram f g cg ch) (graphDiagram f' g' cg' ch') sqf sqg sqh M
  -- The kernel checks the definitional compactification eta conversion directly.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ds := (← Lean.MonadLCtx.getLCtx).decls.toList.filterMap id
    let some h := ds.find? (fun d ↦ d.userName.eraseMacroScopes == `ht) |
      throwError "no diagram equation"
    (← Lean.Elab.Tactic.getMainGoal).assign h.toExpr

private theorem chosenCompactificationExactExchange_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] (sq : IsPullback v f' f b) :
    chosenCompactificationExactExchange A (HasCompactification.compactification f)
        (HasCompactification.compactification f') sq =
      Functor.whiskerLeft R(f)_![ModuleCat.{u + 1} A]
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) b).inv ≫
        rightDerivedLowerShriekBaseChangeMap A sq ≫
        Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).hom
          R(f')_![ModuleCat.{u + 1} A] := by
  rw [chosenCompactificationExactExchange, compactificationExactExchange_transport]
  ext M
  simp only [rightDerivedLowerShriekBaseChangeMap, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  simp only [rightDerivedLowerShriekIso]
  have hn := (rightDerivedLowerShriekOfCompactificationIso A
    ((HasCompactification.compactification f).ofIsPullback sq)
    (HasCompactification.compactification f')).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).hom.app M)
  dsimp only [rightDerivedLowerShriek, Functor.comp_obj] at hn ⊢
  erw [hn]

private theorem change_pullback_compositor
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {F' : C' ⥤ D'} {G' : D' ⥤ E'} {H' : C' ⥤ E'}
    {UL UD : C ⥤ C'} {VL VD : D ⥤ D'} {WL WD : E ⥤ E'}
    (u : UL ≅ UD) (v : VL ≅ VD) (w : WL ≅ WD)
    (ef : F ⋙ VL ⟶ UL ⋙ F') (eg : G ⋙ WL ⟶ VL ⋙ G')
    (eh : H ⋙ WL ⟶ UL ⋙ H') (I : H ≅ F ⋙ G) (I' : H' ≅ F' ⋙ G')
    (h : ∀ M,
      WD.map (I.hom.app M) ≫
          (Functor.whiskerLeft G w.inv ≫ eg ≫ Functor.whiskerRight v.hom G').app
            (F.obj M) ≫
          G'.map ((Functor.whiskerLeft F v.inv ≫ ef ≫
            Functor.whiskerRight u.hom F').app M) =
        (Functor.whiskerLeft H w.inv ≫ eh ≫ Functor.whiskerRight u.hom H').app M ≫
          I'.hom.app (UD.obj M)) (M : C) :
    WL.map (I.hom.app M) ≫ eg.app (F.obj M) ≫ G'.map (ef.app M) =
      eh.app M ≫ I'.hom.app (UL.obj M) := by
  have hh := h M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc] at hh
  have hw := w.inv.naturality (I.hom.app M)
  dsimp only [Functor.comp_obj] at hw
  rw [reassoc_of% hw] at hh
  simp only [← G'.map_comp_assoc, Iso.hom_inv_id_app, G'.map_id,
    Category.id_comp, Iso.hom_inv_id_app_assoc] at hh
  have hn := I'.hom.naturality (u.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [hn] at hh
  apply (cancel_epi (w.inv.app (H.obj M))).1
  apply (cancel_mono (G'.map (F'.map (u.hom.app M)))).1
  simpa only [Category.assoc] using hh

/-- The graph compositor commutes with compact-support exchange for pasted squares.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7F and 0F7J; blueprint
`sec-six-functors-basics/sk-thm-sf-comp-composition`, composition and base change;
steps 4--7 of `lem-route-exists-right-derived-lower-shriek-comp-iso`.
(auxiliary; not a blueprint node).

Proof: form the product of the proper parts of the compactifications of the composite
and of g. Its open over X contains the proper graph of X; its open over Y is proper
over Y; intersect the opens to obtain the graph presentation of f. The graph
compositor consists of the comparison from the compactification of the composite,
the inverse proper/open interchange, and the inverse graph comparison for f.
Pull back this whole diagram along c. For each proper compositor the mate-pasting
identity supplies the exchange square. The unit-normalized open mate supplies the
square for each open compositor. The proper/open exchange cube supplies the square
for each interchange, including the extra graph-neighborhood shrinking. The graph
comparison base-change theorem supplies the squares for the endpoint graph maps
and their inverses. Paste these equalities to obtain the equation with the literal
pulled-back graph diagram. Compare that diagram with the graph constructed from the
chosen primed compactifications. Graph comparison/interchange compatibility and the
graph comparison cocycle identify their compositors. Finally the quasi-compact
refinement clause identifies the comparison from each pulled-back compactification
with rightDerivedLowerShriekIso. Naturality moves the middle comparison across the
exchange for f. Substitution gives the displayed equality. All operations are on
ordinary unbounded derived categories; no quasi-compactness of the original maps
or their open compactification factors is used. -/
theorem sfGraphCompactSupportCompIso_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c)
    (sqh : IsPullback a (f' ≫ g') (f ≫ g) c)
    (M : DerivedCategoryModule A X) :
    L((c)^*[ModuleCat.{u + 1} A]).map
        ((sfGraphCompactSupportCompIso A f g
          (HasCompactification.compactification f)
          (HasCompactification.compactification g)
          (HasCompactification.compactification (f ≫ g))).hom.app M) ≫
      (rightDerivedLowerShriekBaseChangeMap A sqg).app
        (R(f)_![ModuleCat.{u + 1} A].obj M) ≫
      R(g')_![ModuleCat.{u + 1} A].map
        ((rightDerivedLowerShriekBaseChangeMap A sqf).app M) =
    (rightDerivedLowerShriekBaseChangeMap A sqh).app M ≫
      (sfGraphCompactSupportCompIso A f' g'
        (HasCompactification.compactification f')
        (HasCompactification.compactification g')
        (HasCompactification.compactification (f' ≫ g'))).hom.app
          (L((a)^*[ModuleCat.{u + 1} A]).obj M) := by
  apply change_pullback_compositor
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) b)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c)
    (rightDerivedLowerShriekBaseChangeMap A sqf)
    (rightDerivedLowerShriekBaseChangeMap A sqg)
    (rightDerivedLowerShriekBaseChangeMap A sqh)
    (sfGraphCompactSupportCompIso A f g
      (HasCompactification.compactification f)
      (HasCompactification.compactification g)
      (HasCompactification.compactification (f ≫ g)))
    (sfGraphCompactSupportCompIso A f' g'
      (HasCompactification.compactification f')
      (HasCompactification.compactification g')
      (HasCompactification.compactification (f' ≫ g')))
    (fun N ↦ ?_) M
  rw [← chosenCompactificationExactExchange_transport A sqf,
    ← chosenCompactificationExactExchange_transport A sqg,
    ← chosenCompactificationExactExchange_transport A sqh]
  exact graph_chosenExact_comp A
    (HasCompactification.compactification f) (HasCompactification.compactification g)
    (HasCompactification.compactification (f ≫ g))
    (HasCompactification.compactification f') (HasCompactification.compactification g')
    (HasCompactification.compactification (f' ≫ g')) sqf sqg sqh N

end AlgebraicGeometry.Etale
