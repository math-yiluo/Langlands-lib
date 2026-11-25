/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import all WeilConjectures.AlgebraicGeometry.DerivedCompactSupportCompositionCoherence

/-! # Target-square subgrid of ambient projection pasting

Source: Stacks Tags 0F7C, 0F7D and 0F7J, the k-side ambient rectangle.
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
  etaleGraphNormalizedProperOpenExchange

private theorem normalized_cartesian
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
  exact (Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))).2.2.1 k r p i sq

private theorem normalized_vertical
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z S T : Scheme.{u}}
    (k : U ⟶ V) (i₁ : W ⟶ Z) (i₂ : S ⟶ T)
    (r₁ : U ⟶ W) (p₁ : V ⟶ Z) (r₂ : W ⟶ S) (p₂ : Z ⟶ T)
    (r₀ : U ⟶ S) (p₀ : V ⟶ T)
    [IsProper r₁] [IsProper p₁] [IsProper r₂] [IsProper p₂]
    [IsProper r₀] [IsProper p₀]
    [IsOpenImmersion k] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (s₁ : CommSq k r₁ p₁ i₁) (s₂ : CommSq i₁ r₂ p₂ i₂)
    (hr : r₁ ≫ r₂ = r₀) (hp : p₁ ≫ p₂ = p₀)
    (s₀ : CommSq k r₀ p₀ i₂) (M : DerivedCategoryModule A U) :
    (etaleGraphNormalizedProperOpenExchange A k r₀ p₀ i₂ s₀).hom.app M =
      D((i₂)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) r₁ r₂ r₀ hr).inv.app M) ≫
        (etaleGraphNormalizedProperOpenExchange A i₁ r₂ p₂ i₂ s₂).hom.app
          (R((r₁)_*[ModuleCat.{u + 1} A]).obj M) ≫
        R((p₂)_*[ModuleCat.{u + 1} A]).map
          ((etaleGraphNormalizedProperOpenExchange A k r₁ p₁ i₁ s₁).hom.app M) ≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p₁ p₂ p₀ hp).hom.app
          (D((k)_!open[ModuleCat.{u + 1} A]).obj M) := by
  subst r₀
  subst p₀
  dsimp only [rightDerivedLowerStarCompOfEq]
  delta etaleGraphNormalizedProperOpenExchange
  exact (Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))).2.2.2.1
      k i₁ i₂ r₁ p₁ r₂ p₂ s₁ s₂ M

private theorem normalized_horizontal
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V V' W Z Z' : Scheme.{u}}
    (k : U ⟶ V) (l : V ⟶ V') (i : W ⟶ Z) (j : Z ⟶ Z')
    (r : U ⟶ W) (p : V ⟶ Z) (q : V' ⟶ Z') (kl : U ⟶ V')
    [IsProper r] [IsProper p] [IsProper q]
    [IsOpenImmersion k] [IsOpenImmersion l]
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion kl]
    (s₁ : CommSq k r p i) (s₂ : CommSq l p q j) (hkl : k ≫ l = kl)
    (s₀ : CommSq kl r q (i ≫ j)) (M : DerivedCategoryModule A U) :
    (etaleGraphNormalizedProperOpenExchange A kl r q (i ≫ j) s₀).hom.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) i j).hom.app (R((r)_*[ModuleCat.{u + 1} A]).obj M) ≫
        D((j)_!open[ModuleCat.{u + 1} A]).map
          ((etaleGraphNormalizedProperOpenExchange A k r p i s₁).hom.app M) ≫
        (etaleGraphNormalizedProperOpenExchange A l p q j s₂).hom.app
          (D((k)_!open[ModuleCat.{u + 1} A]).obj M) ≫
        R((q)_*[ModuleCat.{u + 1} A]).map
          (((mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) k l).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr
              (ModuleCat.{u + 1} A) hkl).hom.app M) := by
  subst kl
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.trans_refl, Iso.symm_hom]
  delta etaleGraphNormalizedProperOpenExchange
  exact (Classical.choose_spec
    (Classical.choose_spec (etaleProperOpenExchangeCube A))).2.2.2.2.1
      k l i j r p q s₁ s₂ M

private theorem compOfEq_hom
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg h).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom ≫
        eqToHom (congrArg (fun k ↦ R((k)_*[ModuleCat.{u + 1} A])) h) := by
  subst fg
  simp only [rightDerivedLowerStarCompOfEq, eqToHom_refl, Category.comp_id]

private theorem comp_assoc
    (A : Type (u + 1)) [CommRing A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfull : fg ≫ h = fgh)
    (M : DerivedCategoryModule A W) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) g h gh hgh).hom.app
        (R((f)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f gh fgh
        (by rw [← hgh, ← Category.assoc, hfg, hfull])).hom.app M =
    R((h)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg hfg).hom.app M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) fg h fgh hfull).hom.app M := by
  subst fg
  subst gh
  rw [Category.assoc] at hfull
  subst fgh
  simpa only [compOfEq_hom, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.comp_id, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] using congr_app (push_derived_assoc A f g h) M

private theorem compOfEq_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg h =
      rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g ≪≫
        eqToIso (congrArg (fun k ↦ R((k)_*[ModuleCat.{u + 1} A])) h) := by
  subst fg
  simp only [rightDerivedLowerStarCompOfEq, eqToIso_refl, Iso.trans_refl]

private theorem refactor_comp
    (A : Type (u + 1)) [CommRing A]
    {X Y Y' Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (f' : X ⟶ Y') (g' : Y' ⟶ Z) (h : f' ≫ g' = f ≫ g) :
    rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g (f' ≫ g') h.symm ≪≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f' g').symm =
      rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g ≪≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f' g' (f ≫ g) h).symm := by
  rw [compOfEq_eq, compOfEq_eq]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, eqToIso,
    Category.assoc]

-- The rectangle calculation before adjoining the initial graph and final proper map.
private theorem grid_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {H N PH W V P Y T UG PG : Scheme.{u}}
    (E : H ⟶ N) (K : N ⟶ PH) (jH : H ⟶ PH)
    (e : W ⟶ V) (k : V ⟶ P) (i : Y ⟶ T) (jG : UG ⟶ PG)
    (qH : H ⟶ W) (qN : N ⟶ V) (prH : PH ⟶ P)
    (r : V ⟶ Y) (p : P ⟶ T) (R : N ⟶ UG) (qG : UG ⟶ Y)
    (pp : PH ⟶ PG) (prG : PG ⟶ T)
    [IsOpenImmersion E] [IsOpenImmersion K] [IsOpenImmersion jH]
    [IsOpenImmersion e] [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion jG]
    [IsProper qH] [IsProper qN] [IsProper prH] [IsProper r] [IsProper p]
    [IsProper R] [IsProper qG] [IsProper pp] [IsProper prG]
    (se : CommSq E qH qN e) (sk : IsPullback qN K k prH)
    (sh : IsPullback qH jH (e ≫ k) prH) (sg : IsPullback qG jG i prG)
    (sq : CommSq k r p i) (sQ : CommSq K R pp jG)
    (hEK : E ≫ K = jH) (hR : R ≫ qG = qN ≫ r)
    (hP : pp ≫ prG = prH ≫ p) (M : DerivedCategoryModule A H) :
    (etaleGraphNormalizedProperOpenExchange A k r p i sq).hom.app
        (D((e)_!open[ModuleCat.{u + 1} A]).obj
          (R((qH)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) e k).inv.app
            (R((qH)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        ((openImmersionLowerShriekLowerStarExchangeIso A sh).hom.app M) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) prH p).hom.app
        (D((jH)_!open[ModuleCat.{u + 1} A]).obj M) =
    D((i)_!open[ModuleCat.{u + 1} A]).map
        (R((r)_*[ModuleCat.{u + 1} A]).map
          ((etaleGraphNormalizedProperOpenExchange A E qH qN e se).hom.app M)) ≫
      D((i)_!open[ModuleCat.{u + 1} A]).map
        (((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) qN r) ≪≫
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
            R qG (qN ≫ r) hR).symm).hom.app
              (D((E)_!open[ModuleCat.{u + 1} A]).obj M)) ≫
      (openImmersionLowerShriekLowerStarExchangeIso A sg).hom.app
        (R((R)_*[ModuleCat.{u + 1} A]).obj
          (D((E)_!open[ModuleCat.{u + 1} A]).obj M)) ≫
      R((prG)_*[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A K R pp jG sQ).hom.app
          (D((E)_!open[ModuleCat.{u + 1} A]).obj M)) ≫
      R((prG)_*[ModuleCat.{u + 1} A]).map
        (R((pp)_*[ModuleCat.{u + 1} A]).map
          (((mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) E K).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr
              (ModuleCat.{u + 1} A) hEK).hom.app M)) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
        pp prG (prH ≫ p) hP).hom.app
          (D((jH)_!open[ModuleCat.{u + 1} A]).obj M) := by
  let B := ModuleCat.{u + 1} A
  let I := D((i)_!open[B])
  let P := R((p)_*[B])
  let G := R((prG)_*[B])
  let PH := R((prH)_*[B])
  let Q := R((pp)_*[B])
  let S := D((E)_!open[B]).obj M
  let ce := etaleGraphNormalizedProperOpenExchange A E qH qN e se
  let ck := openImmersionLowerShriekLowerStarExchangeIso A sk
  let ch := openImmersionLowerShriekLowerStarExchangeIso A sh
  let cg := openImmersionLowerShriekLowerStarExchangeIso A sg
  let cs := etaleGraphNormalizedProperOpenExchange A k r p i sq
  let cQ := etaleGraphNormalizedProperOpenExchange A K R pp jG sQ
  let o := mapDerivedCategoryOpenImmersionLowerShriekComp B e k
  let o' := (mapDerivedCategoryOpenImmersionLowerShriekComp B E K).symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCongr B hEK
  let cr := rightDerivedLowerStarComp B qN r
  let cr' := rightDerivedLowerStarCompOfEq B R qG (qN ≫ r) hR
  let cp := rightDerivedLowerStarComp B prH p
  let cp' := rightDerivedLowerStarCompOfEq B pp prG (prH ≫ p) hP
  have hh := normalized_horizontal A E K e k qH qN prH jH se
    sk.toCommSq.flip hEK sh.toCommSq.flip M
  rw [normalized_cartesian A jH qH prH (e ≫ k) sh,
    normalized_cartesian A K qN prH k sk] at hh
  change ch.hom.app M = o.hom.app _ ≫ D((k)_!open[B]).map (ce.hom.app M) ≫
    ck.hom.app S ≫ PH.map (o'.hom.app M) at hh
  have hho : o.inv.app _ ≫ ch.hom.app M =
      D((k)_!open[B]).map (ce.hom.app M) ≫ ck.hom.app S ≫ PH.map (o'.hom.app M) := by
    rw [hh, Iso.inv_hom_id_app_assoc]
  let so : CommSq K (qN ≫ r) (prH ≫ p) i := sk.toCommSq.flip.vert_comp sq
  have hv := normalized_vertical A K k i qN prH r p (qN ≫ r) (prH ≫ p)
    sk.toCommSq.flip sq rfl rfl so S
  have hv' := normalized_vertical A K jG i R pp qG prG (qN ≫ r) (prH ≫ p)
    sQ sg.toCommSq.flip hR hP so S
  rw [normalized_cartesian A K qN prH k sk] at hv
  rw [normalized_cartesian A jG qG prG i sg] at hv'
  have rect : cs.hom.app (R((qN)_*[B]).obj S) ≫ P.map (ck.hom.app S) ≫
      cp.hom.app (D((K)_!open[B]).obj S) =
      I.map (cr.hom.app S ≫ cr'.inv.app S) ≫
        cg.hom.app (R((R)_*[B]).obj S) ≫ G.map (cQ.hom.app S) ≫
          cp'.hom.app (D((K)_!open[B]).obj S) := by
    have ht := congrArg (fun z ↦ I.map (cr.hom.app S) ≫ z) (hv.symm.trans hv')
    change I.map (cr.hom.app S) ≫
        (I.map (cr.inv.app S) ≫ cs.hom.app _ ≫ P.map (ck.hom.app S) ≫ cp.hom.app _) =
      I.map (cr.hom.app S) ≫
        (I.map (cr'.inv.app S) ≫ cg.hom.app _ ≫ G.map (cQ.hom.app S) ≫ cp'.hom.app _)
      at ht
    simp only [Category.assoc, ← I.map_comp_assoc, Iso.hom_inv_id_app,
      I.map_id, Category.id_comp] at ht
    simpa only [I.map_comp, Category.assoc] using ht
  change cs.hom.app _ ≫ P.map (o.inv.app _) ≫ P.map (ch.hom.app M) ≫
      cp.hom.app _ =
    I.map (R((r)_*[B]).map (ce.hom.app M)) ≫
      I.map ((cr ≪≫ cr'.symm).hom.app S) ≫ cg.hom.app _ ≫
      G.map (cQ.hom.app S) ≫ G.map (Q.map (o'.hom.app M)) ≫ cp'.hom.app _
  rw [← P.map_comp_assoc, hho]
  simp only [P.map_comp, Category.assoc]
  rw [← reassoc_of% cs.hom.naturality (ce.hom.app M)]
  have hn := cp.hom.naturality (o'.hom.app M)
  simp only [Functor.comp_map] at hn
  rw [hn]
  have hn' := cp'.hom.naturality (o'.hom.app M)
  simp only [Functor.comp_map] at hn'
  rw [hn']
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_map,
    Functor.map_comp, Functor.comp_obj, Category.assoc] using
    congrArg (fun t ↦ I.map (R((r)_*[B]).map (ce.hom.app M)) ≫ t ≫
      R((prH ≫ p)_*[B]).map (o'.hom.app M)) rect

-- Adjoin the graph splitter and the terminal proper map to the core rectangle.
private theorem full_grid
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {H N PH W V P Y T UG PG X Z₀ : Scheme.{u}}
    (E : H ⟶ N) (K : N ⟶ PH) (jH : H ⟶ PH)
    (e : W ⟶ V) (k : V ⟶ P) (i : Y ⟶ T) (jG : UG ⟶ PG)
    (qH : H ⟶ W) (qN : N ⟶ V) (prH : PH ⟶ P)
    (r : V ⟶ Y) (p : P ⟶ T) (R : N ⟶ UG) (qG : UG ⟶ Y)
    (pp : PH ⟶ PG) (prG : PG ⟶ T)
    [IsOpenImmersion E] [IsOpenImmersion K] [IsOpenImmersion jH]
    [IsOpenImmersion e] [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion jG]
    [IsProper qH] [IsProper qN] [IsProper prH] [IsProper r] [IsProper p]
    [IsProper R] [IsProper qG] [IsProper pp] [IsProper prG]
    (se : CommSq E qH qN e) (sk : IsPullback qN K k prH)
    (sh : IsPullback qH jH (e ≫ k) prH) (sg : IsPullback qG jG i prG)
    (sq : CommSq k r p i) (sQ : CommSq K R pp jG)
    (hEK : E ≫ K = jH) (hR : R ≫ qG = qN ≫ r)
    (hP : pp ≫ prG = prH ≫ p)
    (a : X ⟶ W) (z : X ⟶ H) (q : T ⟶ Z₀) (pG : PG ⟶ Z₀) (pH : PH ⟶ Z₀)
    (hz : z ≫ qH = a) (hg : prG ≫ q = pG) (hh : prH ≫ (p ≫ q) = pH)
    (hfinal : pp ≫ pG = pH) (M : DerivedCategoryModule A X) :
    let B := ModuleCat.{u + 1} A
    let M₀ := R((z)_*[B]).obj M
    let S := D((E)_!open[B]).obj M₀
    let Q := R((q)_*[B])
    let P := R((p)_*[B])
    let I := D((i)_!open[B])
    let J := D((e ≫ k)_!open[B])
    let JH := D((jH)_!open[B])
    let c₀ := rightDerivedLowerStarCompOfEq B z qH a hz
    let ce := etaleGraphNormalizedProperOpenExchange A E qH qN e se
    let cs := etaleGraphNormalizedProperOpenExchange A k r p i sq
    let o := mapDerivedCategoryOpenImmersionLowerShriekComp B e k
    let ch := openImmersionLowerShriekLowerStarExchangeIso A sh
    let cg := openImmersionLowerShriekLowerStarExchangeIso A sg
    let cq := etaleGraphNormalizedProperOpenExchange A K R pp jG sQ
    let o' := (mapDerivedCategoryOpenImmersionLowerShriekComp B E K).symm ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekCongr B hEK
    let _cr := rightDerivedLowerStarComp B qN r
    let _cr' := rightDerivedLowerStarCompOfEq B R qG (qN ≫ r) hR
    let _cp := rightDerivedLowerStarComp B prH p
    let _cp' := rightDerivedLowerStarCompOfEq B pp prG (prH ≫ p) hP
    let _ct := rightDerivedLowerStarCompOfEq B (prH ≫ p) q pH
      ((Category.assoc _ _ _).trans hh)
    let cH := rightDerivedLowerStarCompOfEq B prH (p ≫ q) pH hh
    let cG := rightDerivedLowerStarCompOfEq B prG q pG hg
    let cend := rightDerivedLowerStarCompOfEq B pp pG pH hfinal
    let cpq := rightDerivedLowerStarComp B p q
    Q.map (cs.hom.app _) ≫ Q.map (P.map (o.inv.app _)) ≫ cpq.hom.app _ ≫
        R((p ≫ q)_*[B]).map (J.map (c₀.inv.app M)) ≫
        R((p ≫ q)_*[B]).map (ch.hom.app M₀) ≫ cH.hom.app (JH.obj M₀) =
      Q.map (I.map (R((r)_*[B]).map
          (D((e)_!open[B]).map (c₀.inv.app M)) ≫
        R((r)_*[B]).map (ce.hom.app M₀) ≫
          ((rightDerivedLowerStarCompOfEq B qN r (R ≫ qG) hR.symm) ≪≫
            (rightDerivedLowerStarComp B R qG).symm).hom.app S)) ≫
      Q.map (cg.hom.app (R((R)_*[B]).obj S)) ≫ cG.hom.app _ ≫
      R((pG)_*[B]).map (cq.hom.app S) ≫
      R((pG)_*[B]).map (R((pp)_*[B]).map (o'.hom.app M₀)) ≫
      cend.hom.app (JH.obj M₀) := by
  intro B M₀ S Q P I J JH c₀ ce cs o ch cg cq o' cr cr' cp cp' ct cH cG cend cpq
  have href := congrArg (fun α ↦ α.hom.app S) (refactor_comp A qN r R qG hR)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at href ⊢
  rw [href]
  have nh₁ := cpq.hom.naturality (J.map (c₀.inv.app M))
  have nh₂ := cpq.hom.naturality (ch.hom.app M₀)
  simp only [Functor.comp_map] at nh₁ nh₂
  rw [← reassoc_of% nh₁, ← reassoc_of% nh₂]
  have ah := comp_assoc A prH p q (prH ≫ p) (p ≫ q) pH
    rfl rfl ((Category.assoc _ _ _).trans hh) (JH.obj M₀)
  change cpq.hom.app _ ≫ cH.hom.app (JH.obj M₀) =
    Q.map (cp.hom.app (JH.obj M₀)) ≫ ct.hom.app (JH.obj M₀) at ah
  rw [ah]
  have ng₁ := cG.hom.naturality (cq.hom.app S)
  have ng₂ := cG.hom.naturality (R((pp)_*[B]).map (o'.hom.app M₀))
  simp only [Functor.comp_map] at ng₁ ng₂
  rw [← reassoc_of% ng₁, ← reassoc_of% ng₂]
  have ag := comp_assoc A pp prG q (prH ≫ p) pG pH hP hg
    ((Category.assoc _ _ _).trans hh) (JH.obj M₀)
  change cG.hom.app _ ≫ cend.hom.app (JH.obj M₀) =
    Q.map (cp'.hom.app (JH.obj M₀)) ≫ ct.hom.app (JH.obj M₀) at ag
  rw [ag]
  change Q.map (cs.hom.app _) ≫ Q.map (P.map (o.inv.app _)) ≫
      Q.map (P.map (J.map (c₀.inv.app M))) ≫ Q.map (P.map (ch.hom.app M₀)) ≫
      Q.map (cp.hom.app (JH.obj M₀)) ≫ ct.hom.app (JH.obj M₀) =
    Q.map (I.map (R((r)_*[B]).map (D((e)_!open[B]).map (c₀.inv.app M)) ≫
      R((r)_*[B]).map (ce.hom.app M₀) ≫ (cr ≪≫ cr'.symm).hom.app S)) ≫
      Q.map (cg.hom.app (R((R)_*[B]).obj S)) ≫
      Q.map (R((prG)_*[B]).map (cq.hom.app S)) ≫
      Q.map (R((prG)_*[B]).map (R((pp)_*[B]).map (o'.hom.app M₀))) ≫
      Q.map (cp'.hom.app (JH.obj M₀)) ≫ ct.hom.app (JH.obj M₀)
  simp only [← Q.map_comp_assoc]
  apply congrArg (fun t ↦ Q.map t ≫ ct.hom.app (JH.obj M₀))
  have no := o.inv.naturality (c₀.inv.app M)
  simp only [Functor.comp_map] at no
  rw [← P.map_comp_assoc, ← no, P.map_comp, Category.assoc]
  have ns := cs.hom.naturality (D((e)_!open[B]).map (c₀.inv.app M))
  simp only [Functor.comp_map] at ns
  rw [← reassoc_of% ns]
  have hc := grid_core A E K jH e k i jG qH qN prH r p R qG pp prG
    se sk sh sg sq sQ hEK hR hP M₀
  change cs.hom.app _ ≫ P.map (o.inv.app _) ≫ P.map (ch.hom.app M₀) ≫
      cp.hom.app (JH.obj M₀) =
    I.map (R((r)_*[B]).map (ce.hom.app M₀)) ≫
    I.map ((cr ≪≫ cr'.symm).hom.app S) ≫ cg.hom.app _ ≫
    R((prG)_*[B]).map (cq.hom.app S) ≫
    R((prG)_*[B]).map (R((pp)_*[B]).map (o'.hom.app M₀)) ≫
    cp'.hom.app (JH.obj M₀) at hc
  simpa only [Functor.map_comp, Functor.comp_obj, Category.assoc] using
    congrArg (fun t ↦ I.map (R((r)_*[B]).map
      (D((e)_!open[B]).map (c₀.inv.app M))) ≫ t) hc

/-- The supplied k-square commutes with ambient transport through the mixed
neighborhood. No f-side ambient change or inverse B exchange occurs here.

Source: Stacks Tags 0F7C and 0F7D (vertical and horizontal pasting), step 3 of
lem-pur-etale-graph-product-ambient-pasting, and Tag 0F7J, A--F comparison.
(auxiliary; not a blueprint node).

Proof: take the Cartesian k-side square (K,qN,prH,k). Pasting it above the
supplied square gives the same outer commutative square as pasting Q above
the Cartesian g-side square, because R qG=qN r and productP prG=prH p.
Apply vertical pasting to both decompositions and equate the normalized exchanges
for the common outer square. Apply horizontal pasting to the e-side and k-side
squares; the outer square is the Cartesian side square for e k. Substitute the
vertical identity into this horizontal factorization. Whisker by the proper
graph zH and the final proper map q. Naturality moves the graph splitter and
proper compositors past the exchanges; proper-compositor associativity identifies
the two factorizations of the final map. Open-compositor associativity, together
with E K=H.e, gives the target open compositor. These are exactly rawSquare;
ambientLambda on one side, and sourceTransport; middleTail; squareInterchange on
the other. Neither B nor the f-side lambda is used. The argument requires no
nonemptiness or boundedness hypotheses. -/
theorem etaleGraphAmbientSquarePasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (match second with
    | false =>
      let ah := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.compositePresentation d₂.compositePresentation false A
      (EtaleGraphInterchangeDiagram.ProductRow.rawSquare A d₁ ≪≫ ah) =
      (Functor.isoWhiskerRight
          (EtaleGraphInterchangeDiagram.ProductRow.First.sourceTransport d₁ d₂ A)
          (D((d₁.i)_!open[ModuleCat.{u + 1} A]) ⋙
            R((d₁.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (EtaleGraphInterchangeDiagram.ProductRow.First.middleTail d₁ d₂ A) ≪≫
        EtaleGraphInterchangeDiagram.ProductRow.First.squareInterchange d₁ d₂ A)
    | true =>
      let ah := EtaleGraphPresentation.ProductRow.ambientLambda
        d₁.compositePresentation d₂.compositePresentation true A
      (EtaleGraphInterchangeDiagram.ProductRow.rawSquare A d₂ ≪≫ ah) =
      (Functor.isoWhiskerRight
          (EtaleGraphInterchangeDiagram.ProductRow.Second.sourceTransport d₁ d₂ A)
          (D((d₂.i)_!open[ModuleCat.{u + 1} A]) ⋙
            R((d₂.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (EtaleGraphInterchangeDiagram.ProductRow.Second.middleTail d₁ d₂ A) ≪≫
        EtaleGraphInterchangeDiagram.ProductRow.Second.squareInterchange d₁ d₂ A)) := by
  cases second
  · dsimp only
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [EtaleGraphInterchangeDiagram.ProductRow.rawSquare,
      EtaleGraphPresentation.ProductRow.ambientLambda,
      EtaleGraphInterchangeDiagram.ProductRow.First.sourceTransport,
      EtaleGraphInterchangeDiagram.ProductRow.First.middleTail,
      EtaleGraphInterchangeDiagram.ProductRow.First.squareInterchange,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_map, Functor.comp_obj, Category.id_comp, Category.comp_id,
      Category.assoc]
    simp only [EtaleGraphPresentation.functor,
      EtaleGraphInterchangeDiagram.sourcePresentation, Functor.comp_obj, Category.id_comp]
    exact full_grid A
      (EtaleGraphInterchangeDiagram.ProductRow.First.E d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.K d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.H d₁ d₂).e
      d₁.e d₁.k d₁.i (EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).e
      (EtaleGraphPresentation.ProductRow.q
        d₁.compositePresentation d₂.compositePresentation false)
      (EtaleGraphInterchangeDiagram.ProductRow.First.qN d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.prH d₁ d₂)
      d₁.r d₁.p (EtaleGraphInterchangeDiagram.ProductRow.First.R d₁ d₂)
      (EtaleGraphPresentation.ProductRow.q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false)
      (d₁.productP d₂) (EtaleGraphInterchangeDiagram.ProductRow.First.prG d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.e_side_square d₁ d₂)
      (IsPullback.of_hasPullback _ d₁.k).flip
      (IsPullback.of_hasPullback _ (d₁.e ≫ d₁.k)).flip
      (IsPullback.of_hasPullback _ d₁.i).flip d₁.square
      (EtaleGraphInterchangeDiagram.ProductRow.First.Q_square d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.E_K d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.R_q d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.First.productP_projection d₁ d₂)
      d₁.a (EtaleGraphInterchangeDiagram.ProductRow.First.H d₁ d₂).a d₁.q
      (EtaleGraphInterchangeDiagram.ProductRow.First.G d₁ d₂).p
      (EtaleGraphInterchangeDiagram.ProductRow.First.H d₁ d₂).p
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.compositePresentation d₂.compositePresentation false)
      (EtaleGraphPresentation.ProductRow.projection_p
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) false)
      (EtaleGraphPresentation.ProductRow.projection_p
        d₁.compositePresentation d₂.compositePresentation false)
      (d₁.productP_productQ d₂) M
  · dsimp only
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [EtaleGraphInterchangeDiagram.ProductRow.rawSquare,
      EtaleGraphPresentation.ProductRow.ambientLambda,
      EtaleGraphInterchangeDiagram.ProductRow.Second.sourceTransport,
      EtaleGraphInterchangeDiagram.ProductRow.Second.middleTail,
      EtaleGraphInterchangeDiagram.ProductRow.Second.squareInterchange,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_map, Functor.comp_obj, Category.id_comp, Category.comp_id,
      Category.assoc]
    simp only [EtaleGraphPresentation.functor,
      EtaleGraphInterchangeDiagram.sourcePresentation, Functor.comp_obj, Category.id_comp]
    exact full_grid A
      (EtaleGraphInterchangeDiagram.ProductRow.Second.E d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.K d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.H d₁ d₂).e
      d₂.e d₂.k d₂.i (EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).e
      (EtaleGraphPresentation.ProductRow.q
        d₁.compositePresentation d₂.compositePresentation true)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.qN d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.prH d₁ d₂)
      d₂.r d₂.p (EtaleGraphInterchangeDiagram.ProductRow.Second.R d₁ d₂)
      (EtaleGraphPresentation.ProductRow.q
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true)
      (d₁.productP d₂) (EtaleGraphInterchangeDiagram.ProductRow.Second.prG d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.e_side_square d₁ d₂)
      (IsPullback.of_hasPullback _ d₂.k).flip
      (IsPullback.of_hasPullback _ (d₂.e ≫ d₂.k)).flip
      (IsPullback.of_hasPullback _ d₂.i).flip d₂.square
      (EtaleGraphInterchangeDiagram.ProductRow.Second.Q_square d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.E_K d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.R_q d₁ d₂)
      (EtaleGraphInterchangeDiagram.ProductRow.Second.productP_projection d₁ d₂)
      d₂.a (EtaleGraphInterchangeDiagram.ProductRow.Second.H d₁ d₂).a d₂.q
      (EtaleGraphInterchangeDiagram.ProductRow.Second.G d₁ d₂).p
      (EtaleGraphInterchangeDiagram.ProductRow.Second.H d₁ d₂).p
      (EtaleGraphPresentation.ProductRow.z_q
        d₁.compositePresentation d₂.compositePresentation true)
      (EtaleGraphPresentation.ProductRow.projection_p
        (EtaleGraphPresentation.ofCompactification d₁.compactification)
        (EtaleGraphPresentation.ofCompactification d₂.compactification) true)
      (EtaleGraphPresentation.ProductRow.projection_p
        d₁.compositePresentation d₂.compositePresentation true)
      (d₁.productP_productQ d₂) M

end AlgebraicGeometry.Etale
