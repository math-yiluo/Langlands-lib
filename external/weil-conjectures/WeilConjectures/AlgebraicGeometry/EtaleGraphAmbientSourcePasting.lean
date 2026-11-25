/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import all WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition
import all WeilConjectures.AlgebraicGeometry.OpenExchangeTower

/-! # Source-lift subgrid of ambient projection pasting

Source: Stacks Tags 0F7C and 0F7J, the e-side part of the ambient product grid.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem exchange_vertical
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z S T : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (j : S ⟶ T)
    (r : U ⟶ W) (p : V ⟶ Z) (q : W ⟶ S) (s : Z ⟶ T)
    (rq : U ⟶ S) (ps : V ⟶ T)
    [IsProper r] [IsProper p] [IsProper q] [IsProper s] [IsProper ps]
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    (b : CommSq k r p i) (e : CommSq i q s j)
    (f : IsPullback rq k j ps) (hr : r ≫ q = rq) (hp : p ≫ s = ps)
    (M : DerivedCategoryModule A U) :
    (openImmersionLowerShriekLowerStarExchangeIso A f).hom.app M =
      D((j)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) r q rq hr).inv.app M) ≫
        (etaleGraphNormalizedProperOpenExchange A i q s j e).hom.app
          (R((r)_*[ModuleCat.{u + 1} A]).obj M) ≫
        R((s)_*[ModuleCat.{u + 1} A]).map
          ((etaleGraphNormalizedProperOpenExchange A k r p i b).hom.app M) ≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p s ps hp).hom.app
          (D((k)_!open[ModuleCat.{u + 1} A]).obj M) := by
  subst rq
  subst ps
  have hn := (Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))).2.2.1
      k (r ≫ q) (p ≫ s) j f
  have hv := (Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))).2.2.2.1
      k i j r p q s b e M
  simpa only [etaleGraphNormalizedProperOpenExchange, hn,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom,
    rightDerivedLowerStarCompOfEq] using hv

private theorem source_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V W P N L : Scheme.{u}}
    (a : X ⟶ U) (z : X ⟶ V) (h : X ⟶ W)
    (e : U ⟶ P) (k : V ⟶ N) (i : W ⟶ L)
    (bW : V ⟶ W) (qH : W ⟶ U) (qF : V ⟶ U)
    (bV : N ⟶ L) (qN : L ⟶ P) (pr : N ⟶ P)
    [IsOpenImmersion e] [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper bW] [IsProper qH] [IsProper bV] [IsProper qN] [IsProper pr]
    (b : CommSq k bW bV i) (es : CommSq i qH qN e)
    (fs : IsPullback qF k e pr)
    (hz : z ≫ bW = h) (hh : h ≫ qH = a) (hf : z ≫ qF = a)
    (hw : bW ≫ qH = qF) (hv : bV ≫ qN = pr)
    (M : DerivedCategoryModule A X) :
    D((e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) h qH a hh).inv.app M) ≫
      (etaleGraphNormalizedProperOpenExchange A i qH qN e es).hom.app
        (R((h)_*[ModuleCat.{u + 1} A]).obj M) =
    D((e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z qF a hf).inv.app M) ≫
      (openImmersionLowerShriekLowerStarExchangeIso A fs).hom.app
        (R((z)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) bV qN pr hv).inv.app
        (D((k)_!open[ModuleCat.{u + 1} A]).obj
          (R((z)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((qN)_*[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A k bW bV i b).inv.app
          (R((z)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((qN)_*[ModuleCat.{u + 1} A]).map
        (D((i)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z bW h hz).hom.app M)) := by
  let B := ModuleCat.{u + 1} A
  let J := D((e)_!open[B])
  let c := rightDerivedLowerStarCompOfEq B z bW h hz
  let E := etaleGraphNormalizedProperOpenExchange A i qH qN e es
  rw [exchange_vertical A k i e bW bV qH qN qF pr b es fs hw hv]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hs := comp_assoc_inv A z bW qH h qF a hz hw hh M
  have hn := E.hom.naturality (c.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← J.map_comp_assoc, ← hs]
  simp only [c, B, Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  rfl

private theorem proper_tail
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {P N U Y W : Scheme.{u}}
    (pr : P ⟶ U) (r : U ⟶ Y) (p : P ⟶ Y)
    (b : P ⟶ N) (q : N ⟶ U) (t : N ⟶ W) (z : Y ⟶ W) (v : W ⟶ Y)
    (hp : pr ≫ r = p) (hb : b ≫ q = pr) (ht : t ≫ v = q ≫ r)
    (hz : z ≫ v = 𝟙 Y) (hbt : b ≫ t = p ≫ z)
    (M : DerivedCategoryModule A P) :
    R((𝟙 Y)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) pr r p hp).hom.app M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z v (𝟙 Y) hz).inv.app
        (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫
      R((v)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          p z (b ≫ t) hbt.symm).hom.app M) ≫
      R((v)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) b t).inv.app M) =
    (rightDerivedLowerStarIdIso A Y).hom.app
        (R((r)_*[ModuleCat.{u + 1} A]).obj
          (R((pr)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((r)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) b q pr hb).inv.app M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        q r (t ≫ v) ht.symm).hom.app (R((b)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) t v).inv.app
        (R((b)_*[ModuleCat.{u + 1} A]).obj M) := by
  let B := ModuleCat.{u + 1} A
  let cp := rightDerivedLowerStarCompOfEq B pr r p hp
  let cb := rightDerivedLowerStarCompOfEq B b q pr hb
  let cq := rightDerivedLowerStarCompOfEq B q r (t ≫ v) ht.symm
  let cf := rightDerivedLowerStarCompOfEq B b (t ≫ v) p
    (by rw [ht, ← Category.assoc, hb, hp])
  let ct := rightDerivedLowerStarCompOfEq B (b ≫ t) v p
    (by rw [Category.assoc, ht, ← Category.assoc, hb, hp])
  let n := rightDerivedLowerStarIdIso A Y
  have h₁ := comp_assoc A p z v (b ≫ t) (𝟙 Y) p hbt.symm hz
    (by rw [Category.assoc, ht, ← Category.assoc, hb, hp]) M
  have h₂ := comp_assoc_inv A b t v (b ≫ t) (t ≫ v) p rfl rfl
    (by rw [Category.assoc, ht, ← Category.assoc, hb, hp]) M
  have h₃ := comp_assoc A b q r pr (t ≫ v) p hb ht.symm hp M
  have hu : (rightDerivedLowerStarCompOfEq B p (𝟙 Y) p
      (Category.comp_id p)).hom.app M = n.hom.app (R((p)_*[B]).obj M) := by
    have h := congr_app (direct_image_right_unit A p) M
    change (rightDerivedLowerStarComp B p (𝟙 Y)).hom.app M = _
    change (rightDerivedLowerStarComp B p (𝟙 Y)).hom.app M =
      n.hom.app _ ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h
  change _ ≫ _ ≫ _ ≫ _ = n.hom.app _ ≫ R((r)_*[B]).map (cb.inv.app M) ≫
    cq.hom.app _ ≫ (rightDerivedLowerStarComp B t v).inv.app _
  have h₁' := congrArg
    (fun m ↦ (rightDerivedLowerStarCompOfEq B z v (𝟙 Y) hz).inv.app
      (R((p)_*[B]).obj M) ≫ m ≫ ct.inv.app M) h₁
  dsimp only [B, ct] at h₁'
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app,
    Category.comp_id] at h₁'
  rw [← reassoc_of% h₁', hu]
  have hn := n.hom.naturality (cp.hom.app M)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  change n.hom.app _ ≫ cp.hom.app M ≫ ct.inv.app M ≫
      R((v)_*[B]).map ((rightDerivedLowerStarComp B b t).inv.app M) = _
  change ct.inv.app M ≫ R((v)_*[B]).map
      ((rightDerivedLowerStarComp B b t).inv.app M) =
    cf.inv.app M ≫ (rightDerivedLowerStarComp B t v).inv.app _ at h₂
  rw [h₂]
  have h₃' := congrArg
    (fun m ↦ R((r)_*[B]).map (cb.inv.app M) ≫ m ≫ cf.inv.app M) h₃
  dsimp only [B, cb, cf] at h₃'
  simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app, Category.comp_id] at h₃'
  rw [← reassoc_of% h₃']

private theorem source_grid
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V W P N L Y G : Scheme.{u}}
    (a : X ⟶ U) (z : X ⟶ V) (h : X ⟶ W)
    (e : U ⟶ P) (k : V ⟶ N) (i : W ⟶ L)
    (bW : V ⟶ W) (qH : W ⟶ U) (qF : V ⟶ U)
    (bV : N ⟶ L) (qN : L ⟶ P) (pr : N ⟶ P)
    (r : P ⟶ Y) (p : N ⟶ Y) (t : L ⟶ G) (zG : Y ⟶ G) (v : G ⟶ Y)
    [IsOpenImmersion e] [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper bW] [IsProper qH] [IsProper bV] [IsProper qN] [IsProper pr]
    (b : CommSq k bW bV i) (es : CommSq i qH qN e)
    (fs : IsPullback qF k e pr)
    (hz : z ≫ bW = h) (hh : h ≫ qH = a) (hf : z ≫ qF = a)
    (hw : bW ≫ qH = qF) (hv : bV ≫ qN = pr)
    (hp : pr ≫ r = p) (ht : t ≫ v = qN ≫ r)
    (hzG : zG ≫ v = 𝟙 Y) (hbt : bV ≫ t = p ≫ zG)
    (M : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let J := D((e)_!open[B])
    let Jk := D((k)_!open[B])
    let Ji := D((i)_!open[B])
    let P := R((r)_*[B])
    let Q := R((v)_*[B])
    let T := R((t)_*[B])
    let I := R((𝟙 Y)_*[B])
    let Z := R((z)_*[B])
    let H := R((h)_*[B])
    let cH := rightDerivedLowerStarCompOfEq B h qH a hh
    let cF := rightDerivedLowerStarCompOfEq B z qF a hf
    let cW := rightDerivedLowerStarCompOfEq B z bW h hz
    let cP := rightDerivedLowerStarCompOfEq B pr r p hp
    let cG := rightDerivedLowerStarCompOfEq B zG v (𝟙 Y) hzG
    let cT := rightDerivedLowerStarCompOfEq B qN r (t ≫ v) ht.symm
    let cR := rightDerivedLowerStarComp B t v
    let cZ := rightDerivedLowerStarCompOfEq B p zG (bV ≫ t) hbt.symm
    let cB := rightDerivedLowerStarComp B bV t
    let E := etaleGraphNormalizedProperOpenExchange A i qH qN e es
    let F := openImmersionLowerShriekLowerStarExchangeIso A fs
    let S := etaleGraphNormalizedProperOpenExchange A k bW bV i b
    (rightDerivedLowerStarIdIso A Y).hom.app (P.obj (J.obj (R((a)_*[B]).obj M))) ≫
        𝟙 (P.obj (J.obj (R((a)_*[B]).obj M))) ≫
        P.map (J.map (cH.inv.app M)) ≫ P.map (E.hom.app (H.obj M)) ≫
        cT.hom.app (Ji.obj (H.obj M)) ≫ cR.inv.app (Ji.obj (H.obj M)) =
      I.map (P.map (J.map (cF.inv.app M))) ≫ I.map (P.map (F.hom.app (Z.obj M))) ≫
        I.map (cP.hom.app (Jk.obj (Z.obj M))) ≫ cG.inv.app (R((p)_*[B]).obj
          (Jk.obj (Z.obj M))) ≫
        Q.map (𝟙 (R((zG)_*[B]).obj (R((p)_*[B]).obj (Jk.obj (Z.obj M))))) ≫
        Q.map (cZ.hom.app (Jk.obj (Z.obj M))) ≫
        Q.map (cB.inv.app (Jk.obj (Z.obj M))) ≫
        Q.map (T.map (S.inv.app (Z.obj M))) ≫
        Q.map (T.map (Ji.map (cW.hom.app M))) := by
  dsimp only
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, Category.id_comp]
  let B := ModuleCat.{u + 1} A
  let J := D((e)_!open[B])
  let Ji := D((i)_!open[B])
  let P := R((r)_*[B])
  let Q := R((v)_*[B])
  let T := R((t)_*[B])
  let I := R((𝟙 Y)_*[B])
  let n := rightDerivedLowerStarIdIso A Y
  let cH := rightDerivedLowerStarCompOfEq B h qH a hh
  let cF := rightDerivedLowerStarCompOfEq B z qF a hf
  let cW := rightDerivedLowerStarCompOfEq B z bW h hz
  let cT := rightDerivedLowerStarCompOfEq B qN r (t ≫ v) ht.symm
  let cR := rightDerivedLowerStarComp B t v
  let E := etaleGraphNormalizedProperOpenExchange A i qH qN e es
  let F := openImmersionLowerShriekLowerStarExchangeIso A fs
  let S := etaleGraphNormalizedProperOpenExchange A k bW bV i b
  let s := J.map (cF.inv.app M) ≫ F.hom.app (R((z)_*[B]).obj M)
  let w := S.inv.app (R((z)_*[B]).obj M) ≫ Ji.map (cW.hom.app M)
  have hc := source_core A a z h e k i bW qH qF bV qN pr b es fs hz hh hf hw hv M
  have ht' := proper_tail A pr r p bV qN t zG v hp hv ht hzG hbt
    (D((k)_!open[B]).obj (R((z)_*[B]).obj M))
  rw [reassoc_of% ht']
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Functor.comp_obj]
  change n.hom.app _ ≫ P.map (J.map (cH.inv.app M) ≫ E.hom.app _) ≫
      cT.hom.app _ ≫ cR.inv.app _ =
    I.map (P.map s) ≫ n.hom.app _ ≫ P.map _ ≫ cT.hom.app _ ≫
      cR.inv.app _ ≫ Q.map (T.map w)
  have hn := n.hom.naturality (P.map s)
  simp only [Functor.id_map] at hn
  dsimp only [Functor.comp_obj] at hn ⊢
  rw [reassoc_of% hn]
  have hr := cR.inv.naturality w
  have ht'' := cT.hom.naturality w
  simp only [Functor.comp_map, Functor.comp_obj] at hr ht''
  rw [← hr, ← reassoc_of% ht'']
  simp only [← P.map_comp_assoc]
  simpa only [s, w, Functor.map_comp, Category.assoc] using
    congrArg (fun m ↦ n.hom.app _ ≫ P.map m ≫ cT.hom.app _ ≫ cR.inv.app _) hc

/-- The e-side lift agrees with the source ambient change followed by the inverse B
exchange. This statement contains no exchange for the supplied k-square or for Q.

Source: Stacks Tag 0F7C (vertical pasting), applied to step 2 of
lem-pur-etale-graph-product-ambient-pasting; Tag 0F7J, A--F comparison.
(auxiliary; not a blueprint node).

Proof: paste B above the e-side square. Their proper left composite is BW qH=qF,
and their proper right composite is BV qN=prF, by the two pullback projections.
The outer square is the Cartesian f-side square. Replace its Cartesian exchange
by the normalized exchange and expand vertical pasting. Multiply by the inverse
B exchange to solve for the e-side exchange. Whisker by the proper initial graph
and the final proper maps. Naturality moves each proper compositor past the
adjacent exchange. Use zF BW=zH and zH qH=a to identify the initial proper
compositors, and BV R=F.p zG and R qG=qN r to identify the final ones.
Associativity of the fixed direct-image compositors gives the displayed words;
the identity compositor at Y gives rightDerivedLowerStarIdIso. This calculation
uses only the e/B grid, not the original square or any k-side exchange. Empty
schemes cause no exception, as all steps are functorial identities. -/
theorem etaleGraphAmbientSourcePasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (match second with
    | false =>
      let af := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.sourcePresentation d₂.sourcePresentation false A
      let qg := EtaleGraphPresentation.ProductRow.q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false
      let cg := (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).a qg (𝟙 Y)
        (EtaleGraphPresentation.ProductRow.z_q
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) false)).symm
      (Functor.isoWhiskerLeft (d₁.sourcePresentation.functor A)
          (rightDerivedLowerStarIdIso A Y) ≪≫
        Functor.rightUnitor _ ≪≫
        EtaleGraphInterchangeDiagram.ProductRow.First.sourceTransport d₁ d₂ A) =
      (Functor.isoWhiskerRight af R((𝟙 Y)_*[ModuleCat.{u + 1} A]) ≪≫
        Functor.isoWhiskerLeft _ cg ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (EtaleGraphInterchangeDiagram.ProductRow.First.liftInterchange d₁ d₂ A)
          R((qg)_*[ModuleCat.{u + 1} A]))
    | true =>
      let af := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.sourcePresentation d₂.sourcePresentation true A
      let qg := EtaleGraphPresentation.ProductRow.q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true
      let cg := (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        (EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).a qg (𝟙 Y)
        (EtaleGraphPresentation.ProductRow.z_q
          (EtaleGraphPresentation.ofCompactification d₁.compactification)
          (EtaleGraphPresentation.ofCompactification d₂.compactification) true)).symm
      (Functor.isoWhiskerLeft (d₂.sourcePresentation.functor A)
          (rightDerivedLowerStarIdIso A Y) ≪≫
        Functor.rightUnitor _ ≪≫
        EtaleGraphInterchangeDiagram.ProductRow.Second.sourceTransport d₁ d₂ A) =
      (Functor.isoWhiskerRight af R((𝟙 Y)_*[ModuleCat.{u + 1} A]) ≪≫
        Functor.isoWhiskerLeft _ cg ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (EtaleGraphInterchangeDiagram.ProductRow.Second.liftInterchange d₁ d₂ A)
          R((qg)_*[ModuleCat.{u + 1} A]))) := by
  cases second
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    have hv : EtaleGraphInterchangeDiagram.ProductRow.First.BV d₁ d₂ ≫
        EtaleGraphInterchangeDiagram.ProductRow.First.qN d₁ d₂ =
          EtaleGraphInterchangeDiagram.ProductRow.First.prF d₁ d₂ :=
      pullback.lift_snd _ _ _
    have hg := source_grid A d₁.a
      (EtaleGraphInterchangeDiagram.ProductRow.First.F d₁ d₂).a
      (EtaleGraphInterchangeDiagram.ProductRow.First.H d₁ d₂).a
      d₁.e (EtaleGraphInterchangeDiagram.ProductRow.First.F d₁ d₂).e
      (EtaleGraphInterchangeDiagram.ProductRow.First.E d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.BW d₁ d₂)
      (EtaleGraphPresentation.ProductRow.q
        d₁.compositePresentation d₂.compositePresentation false)
      (EtaleGraphPresentation.ProductRow.q
        d₁.sourcePresentation d₂.sourcePresentation false)
      (EtaleGraphInterchangeDiagram.ProductRow.First.BV d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.qN d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.prF d₁ d₂)
      d₁.r (EtaleGraphInterchangeDiagram.ProductRow.First.F d₁ d₂).p
      (EtaleGraphInterchangeDiagram.ProductRow.First.R d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).a
      (EtaleGraphPresentation.ProductRow.q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false)
      (EtaleGraphInterchangeDiagram.ProductRow.First.B_square d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.e_side_square d₁ d₂)
      (IsPullback.of_hasPullback
        (EtaleGraphInterchangeDiagram.ProductRow.First.prF d₁ d₂) d₁.e).flip
      (EtaleGraphInterchangeDiagram.ProductRow.First.a_BW d₁ d₂)
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.compositePresentation d₂.compositePresentation false)
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.sourcePresentation d₂.sourcePresentation false)
      (EtaleGraphInterchangeDiagram.ProductRow.First.BW_q d₁ d₂) hv
      (EtaleGraphInterchangeDiagram.ProductRow.First.prF_r d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.R_q d₁ d₂)
      (EtaleGraphPresentation.ProductRow.z_q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false)
      (EtaleGraphInterchangeDiagram.ProductRow.First.BV_R d₁ d₂) M
    simp only [EtaleGraphInterchangeDiagram.ProductRow.First.sourceTransport,
      EtaleGraphInterchangeDiagram.ProductRow.First.liftInterchange,
      EtaleGraphPresentation.ProductRow.ambientLambda,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_hom_app, Functor.comp_map, Functor.map_comp,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      Category.assoc]
    exact hg
  · apply Iso.ext
    apply NatTrans.ext
    funext M
    have hv : EtaleGraphInterchangeDiagram.ProductRow.Second.BV d₁ d₂ ≫
        EtaleGraphInterchangeDiagram.ProductRow.Second.qN d₁ d₂ =
          EtaleGraphInterchangeDiagram.ProductRow.Second.prF d₁ d₂ :=
      pullback.lift_snd _ _ _
    have hg := source_grid A d₂.a
      (EtaleGraphInterchangeDiagram.ProductRow.Second.F d₁ d₂).a
      (EtaleGraphInterchangeDiagram.ProductRow.Second.H d₁ d₂).a
      d₂.e (EtaleGraphInterchangeDiagram.ProductRow.Second.F d₁ d₂).e
      (EtaleGraphInterchangeDiagram.ProductRow.Second.E d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.BW d₁ d₂)
      (EtaleGraphPresentation.ProductRow.q
        d₁.compositePresentation d₂.compositePresentation true)
      (EtaleGraphPresentation.ProductRow.q
        d₁.sourcePresentation d₂.sourcePresentation true)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.BV d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.qN d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.prF d₁ d₂)
      d₂.r (EtaleGraphInterchangeDiagram.ProductRow.Second.F d₁ d₂).p
      (EtaleGraphInterchangeDiagram.ProductRow.Second.R d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).a
      (EtaleGraphPresentation.ProductRow.q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.B_square d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.e_side_square d₁ d₂)
      (IsPullback.of_hasPullback
        (EtaleGraphInterchangeDiagram.ProductRow.Second.prF d₁ d₂) d₂.e).flip
      (EtaleGraphInterchangeDiagram.ProductRow.Second.a_BW d₁ d₂)
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.compositePresentation d₂.compositePresentation true)
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.sourcePresentation d₂.sourcePresentation true)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.BW_q d₁ d₂) hv
      (EtaleGraphInterchangeDiagram.ProductRow.Second.prF_r d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.R_q d₁ d₂)
      (EtaleGraphPresentation.ProductRow.z_q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.BV_R d₁ d₂) M
    simp only [EtaleGraphInterchangeDiagram.ProductRow.Second.sourceTransport,
      EtaleGraphInterchangeDiagram.ProductRow.Second.liftInterchange,
      EtaleGraphPresentation.ProductRow.ambientLambda,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_hom_app, Functor.comp_map, Functor.map_comp,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      Category.assoc]
    exact hg
end AlgebraicGeometry.Etale
