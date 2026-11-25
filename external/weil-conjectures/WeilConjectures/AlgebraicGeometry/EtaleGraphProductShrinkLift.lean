/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkWords
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import all WeilConjectures.AlgebraicGeometry.SfExactExchangePasting

/-! # Shrinking the inverse B exchange

Source: Stacks Project, Tags 0F7C, 0F7D and the A--F calculation of Tag 0F7J.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open EtaleGraphInterchangeDiagram.ProductShrink

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem graph_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U U' W W' : Scheme.{u}}
    (a : X ⟶ U) (a' : X ⟶ U') (b : X ⟶ W) (b' : X ⟶ W')
    (v : U' ⟶ U) (w : W' ⟶ W) (r : U ⟶ W) (r' : U' ⟶ W')
    [IsProper a] [IsProper a'] [IsProper b] [IsProper b']
    [IsProper r] [IsProper r'] [IsOpenImmersion v] [IsOpenImmersion w]
    (hv : a' ≫ v = a) (hw : b' ≫ w = b)
    (hr : a ≫ r = b) (hr' : a' ≫ r' = b') (sq : CommSq v r' r w)
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a r b hr).hom.app M ≫
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A b' w b hw).inv.app M =
    R((r)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v a hv).inv.app M) ≫
      (etaleGraphNormalizedProperOpenExchange A v r' r w sq).inv.app
        (R((a')_*[ModuleCat.{u + 1} A]).obj M) ≫
      D((w)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a' r' b' hr').hom.app M) := by
  cases hr
  cases hr'
  let st : IsPullback a' (𝟙 X) v a :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hv⟩
  let so : IsPullback (a' ≫ r') (𝟙 X) w (a ≫ r) :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hw⟩
  have hs := Classical.choose_spec (Classical.choose_spec (etaleProperOpenExchangeCube A))
  have hp := hs.2.2.2.1 (𝟙 X) v w a' a r' r st.toCommSq.flip sq M
  have ht := hs.2.2.1 (𝟙 X) a' a v st
  have ho := hs.2.2.1 (𝟙 X) (a' ≫ r') (a ≫ r) w so
  rw [ht, ho] at hp
  have hnorm :
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A (a' ≫ r') w
        (a ≫ r) hw).hom.app M =
      D((w)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) a' r').inv.app M) ≫
        (etaleGraphNormalizedProperOpenExchange A v r' r w sq).hom.app
          (R((a')_*[ModuleCat.{u + 1} A]).obj M) ≫
        R((r)_*[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v a hv).hom.app M) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) a r).hom.app M := by
    simp only [rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      openImmersionLowerShriekLowerStarExchangeIso, asIso_hom, Functor.comp_obj,
      Functor.id_obj, Category.comp_id]
    rw [hp]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) a r).hom.naturality]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  have hinv := IsIso.inv_eq_inv.mpr hnorm
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at hinv
  simp only [rightDerivedLowerStarCompOfEq, Iso.symm_inv, Iso.symm_hom]
  rw [hinv]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, NatIso.inv_inv_app]

private def open_comp
    (A : Type (u + 1)) [CommRing A] {U V W : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k] (h : i ≫ j = k) :=
  mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h.symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j

private theorem open_comp_inv
    (A : Type (u + 1)) [CommRing A] {U V W : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k] (h : i ≫ j = k) :
    (open_comp A i j k h).inv =
      (mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} A) i j).inv ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).hom := by
  cases h
  rfl

private theorem open_unit_right
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (M : DerivedCategoryModule A U) :
    (open_comp A j (𝟙 V) j (Category.comp_id j)).hom.app M ≫
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) V).hom.app
        (D((j)_!open[ModuleCat.{u + 1} A]).obj M) = 𝟙 _ := by
  have h := congr_app ((unboundedFormalism A).shComp'_id_right j) M
  rw [unbounded_sh_comp, graph_sh_id] at h
  dsimp only [unboundedFormalism] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, NatTrans.id_app, Functor.comp_obj,
    Functor.id_obj] at h
  simpa only [open_comp, Category.comp_id] using h

private theorem horizontal_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V V' W Z Z' : Scheme.{u}}
    (k : U ⟶ V) (l : V ⟶ V') (i : W ⟶ Z) (j : Z ⟶ Z')
    (kl : U ⟶ V') (ij : W ⟶ Z') (r : U ⟶ W) (p : V ⟶ Z) (q : V' ⟶ Z')
    [IsProper r] [IsProper p] [IsProper q] [IsOpenImmersion k] [IsOpenImmersion l]
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion kl] [IsOpenImmersion ij]
    (hk : k ≫ l = kl) (hi : i ≫ j = ij)
    (s : CommSq k r p i) (t : CommSq l p q j) (o : CommSq kl r q ij)
    (M : DerivedCategoryModule A U) :
    (etaleGraphNormalizedProperOpenExchange A kl r q ij o).hom.app M =
      (open_comp A i j ij hi).hom.app (R((r)_*[ModuleCat.{u + 1} A]).obj M) ≫
      D((j)_!open[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A k r p i s).hom.app M) ≫
      (etaleGraphNormalizedProperOpenExchange A l p q j t).hom.app
        (D((k)_!open[ModuleCat.{u + 1} A]).obj M) ≫
      R((q)_*[ModuleCat.{u + 1} A]).map ((open_comp A k l kl hk).inv.app M) := by
  cases hk
  cases hi
  have hs := Classical.choose_spec (Classical.choose_spec (etaleProperOpenExchangeCube A))
  simp only [open_comp, mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_trans]
  exact hs.2.2.2.2.1 k l i j r p q s t M

private theorem horizontal_shrink
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' W W' P N N' : Scheme.{u}}
    (v : U' ⟶ U) (w : W' ⟶ W) (e : U ⟶ P) (e' : U' ⟶ P)
    (j : W ⟶ N) (j' : W' ⟶ N') (n : N' ⟶ N)
    (b : U ⟶ W) (b' : U' ⟶ W') (c : P ⟶ N) (c' : P ⟶ N')
    [IsOpenImmersion v] [IsOpenImmersion w] [IsOpenImmersion e]
    [IsOpenImmersion e'] [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion n]
    [IsProper b] [IsProper b'] [IsProper c] [IsProper c']
    (hv : v ≫ e = e') (hw : w ≫ j = j' ≫ n) (hc : c' ≫ n = c)
    (s : CommSq v b' b w) (a : CommSq e b c j) (a' : CommSq e' b' c' j')
    (M : DerivedCategoryModule A U') :
    (etaleGraphNormalizedProperOpenExchange A e b c j a).inv.app
        (D((v)_!open[ModuleCat.{u + 1} A]).obj M) ≫
      D((j)_!open[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A v b' b w s).inv.app M) ≫
      ((mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) w j).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hw ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) j' n).hom.app
            (R((b')_*[ModuleCat.{u + 1} A]).obj M) =
    R((c)_*[ModuleCat.{u + 1} A]).map ((open_comp A v e e' hv).inv.app M) ≫
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A c' n c hc).inv.app
        (D((e')_!open[ModuleCat.{u + 1} A]).obj M) ≫
      D((n)_!open[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A e' b' c' j' a').inv.app M) := by
  let t : IsPullback c' (𝟙 P) n c :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hc⟩
  let o : CommSq e' b' c (w ≫ j) := ⟨by
    rw [← hv, Category.assoc, a.w, ← Category.assoc, s.w, Category.assoc]⟩
  have h₁ := horizontal_pasting A v e w j e' (w ≫ j) b' b c hv rfl s a o M
  have h₂ := horizontal_pasting A e' (𝟙 P) j' n e' (w ≫ j) b' c' c
    (Category.comp_id e') hw.symm a' t.toCommSq.flip o M
  have hs := Classical.choose_spec (Classical.choose_spec (etaleProperOpenExchangeCube A))
  have ht := hs.2.2.1 (𝟙 P) c' c n t
  change (etaleGraphNormalizedProperOpenExchange A (𝟙 P) c' c n
    t.toCommSq.flip).hom = _ at ht
  rw [ht] at h₂
  have hu := open_unit_right A e' M
  have hui : (open_comp A e' (𝟙 P) e' (Category.comp_id e')).inv.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) P).hom.app
        (D((e')_!open[ModuleCat.{u + 1} A]).obj M) := by
    apply (cancel_epi ((open_comp A e' (𝟙 P) e' (Category.comp_id e')).hom.app M)).1
    simpa only [Iso.hom_inv_id_app] using hu.symm
  rw [hui] at h₂
  have htri : (openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} A) t).app (D((e')_!open[ModuleCat.{u + 1} A]).obj M) ≫
      R((c)_*[ModuleCat.{u + 1} A]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) P).hom.app
          (D((e')_!open[ModuleCat.{u + 1} A]).obj M)) =
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A c' n c hc).hom.app
        (D((e')_!open[ModuleCat.{u + 1} A]).obj M) := by
    simp only [rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      openImmersionLowerShriekLowerStarExchangeIso, asIso_hom, Functor.comp_obj,
      Functor.id_obj, Category.comp_id]
  rw [htri] at h₂
  have hraw := h₁.symm.trans h₂
  have hinv := IsIso.inv_eq_inv.mpr hraw
  have hh := congrArg
    (fun z ↦ R((c)_*[ModuleCat.{u + 1} A]).map
        ((open_comp A v e e' hv).inv.app M) ≫ z ≫
      (open_comp A j' n (w ≫ j) hw.symm).hom.app
        (R((b')_*[ModuleCat.{u + 1} A]).obj M)) hinv
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    NatIso.inv_inv_app, Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id] at hh
  simp only [open_comp, mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_trans, Iso.trans_hom, Iso.trans_inv, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, NatTrans.comp_app,
    Iso.symm_hom, Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc] at hh ⊢
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hh

private theorem triangle_precomp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z Z' : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) (q' : Y ⟶ Z')
    (v : Z' ⟶ Z) (b : X ⟶ Z) (b' : X ⟶ Z')
    [IsProper p] [IsProper q] [IsProper q'] [IsProper b] [IsProper b']
    [IsOpenImmersion v] (hv : q' ≫ v = q)
    (hb : p ≫ q = b) (hb' : p ≫ q' = b') (h : b' ≫ v = b)
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A b' v b h).hom.app M =
      D((v)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p q' b' hb').inv.app M) ≫
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A q' v q hv).hom.app
        (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p q b hb).hom.app M := by
  cases hb
  cases hb'
  let si : CommSq (𝟙 X) p p (𝟙 Y) := ⟨by simp only [Category.id_comp, Category.comp_id]⟩
  let st : IsPullback q' (𝟙 Y) v q :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hv⟩
  let so : IsPullback (p ≫ q') (𝟙 X) v (p ≫ q) :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using h⟩
  have hs := Classical.choose_spec (Classical.choose_spec (etaleProperOpenExchangeCube A))
  have hp := hs.2.2.2.1 (𝟙 X) (𝟙 Y) v p p q' q si st.toCommSq.flip M
  rw [hs.2.2.1 (𝟙 X) (p ≫ q') (p ≫ q) v so,
    hs.2.2.1 (𝟙 Y) q' q v st, hs.2.2.2.2.2.2.1 p si M] at hp
  simp only [rightDerivedLowerStarCompOfEq,
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom, Functor.comp_obj,
    Functor.id_obj, Category.comp_id]
  rw [hp]
  simp only [Category.assoc]
  rw [← (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p q).hom.naturality]
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id, Functor.id_obj]

private theorem middle_graph
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y N N' U U' : Scheme.{u}}
    (p : X ⟶ Y) (q : Y ⟶ U) (q' : Y ⟶ U') (k : U' ⟶ U)
    (c : X ⟶ N) (c' : X ⟶ N') (n : N' ⟶ N)
    (r : N ⟶ U) (r' : N' ⟶ U')
    [IsProper p] [IsProper q] [IsProper q'] [IsProper c] [IsProper c']
    [IsProper r] [IsProper r'] [IsOpenImmersion k] [IsOpenImmersion n]
    (hq : q' ≫ k = q) (hc : c' ≫ n = c)
    (h : p ≫ q = c ≫ r) (h' : p ≫ q' = c' ≫ r')
    (sq : CommSq n r' r k) (M : DerivedCategoryModule A X) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p q (c ≫ r) h).hom.app M ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c r).inv.app M ≫
      R((r)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A c' n c hc).inv.app M) ≫
      (etaleGraphNormalizedProperOpenExchange A n r' r k sq).inv.app
        (R((c')_*[ModuleCat.{u + 1} A]).obj M) =
    (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A q' k q hq).inv.app
        (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫
      D((k)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p q' (c' ≫ r') h').hom.app M) ≫
      D((k)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c' r').inv.app M) := by
  have hw : (c' ≫ r') ≫ k = c ≫ r := by
    rw [Category.assoc, ← sq.w, ← Category.assoc, hc]
  have hg := graph_square A c c' (c ≫ r) (c' ≫ r') n k r r' hc hw rfl rfl sq M
  have ht := triangle_precomp A p q q' k (c ≫ r) (c' ≫ r') hq h h' hw M
  have hi := IsIso.inv_eq_inv.mpr ht
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    NatIso.inv_inv_app] at hi
  apply (cancel_mono (D((k)_!open[ModuleCat.{u + 1} A]).map
    ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c' r').hom.app M))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [rightDerivedLowerStarCompOfEq] at hg
  rw [← hg]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hi]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem ambient_a_BW
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (b : Bool) :
    (F d₁ d₂ b).a ≫ BW d₁ d₂ b = (H d₁ d₂ b).a := by
  cases b
  · exact EtaleGraphInterchangeDiagram.ProductRow.First.a_BW d₁ d₂
  · exact EtaleGraphInterchangeDiagram.ProductRow.Second.a_BW d₁ d₂

private theorem ambient_BV_R
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (b : Bool) :
    BV d₁ d₂ b ≫ R d₁ d₂ b = (F d₁ d₂ b).p ≫ (G d₁ d₂ b).a := by
  cases b
  · exact EtaleGraphInterchangeDiagram.ProductRow.First.BV_R d₁ d₂
  · exact EtaleGraphInterchangeDiagram.ProductRow.Second.BV_R d₁ d₂

private theorem ambient_B_square
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (b : Bool) :
    CommSq (F d₁ d₂ b).e (BW d₁ d₂ b) (BV d₁ d₂ b) (E d₁ d₂ b) := by
  cases b
  · exact EtaleGraphInterchangeDiagram.ProductRow.First.B_square d₁ d₂
  · exact EtaleGraphInterchangeDiagram.ProductRow.Second.B_square d₁ d₂

private def bridge
    (A : Type (u + 1)) [CommRing A]
    {X Y N U : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ U) (c : X ⟶ N) (r : N ⟶ U)
    (h : p ≫ q = c ≫ r) :=
  rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) p q (c ≫ r) h ≪≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c r).symm

private theorem lift_formula
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (b : Bool)
    (M : DerivedCategoryModule A X) :
    (liftInterchange d₁ d₂ b A).hom.app M =
      (bridge A (F d₁ d₂ b).p (G d₁ d₂ b).a (BV d₁ d₂ b) (R d₁ d₂ b)
        (ambient_BV_R d₁ d₂ b).symm).hom.app
          (D(((F d₁ d₂ b).e)_!open[ModuleCat.{u + 1} A]).obj
            (R(((F d₁ d₂ b).a)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((R d₁ d₂ b)_*[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A (F d₁ d₂ b).e
          (BW d₁ d₂ b) (BV d₁ d₂ b) (E d₁ d₂ b)
          (ambient_B_square d₁ d₂ b)).inv.app
            (R(((F d₁ d₂ b).a)_*[ModuleCat.{u + 1} A]).obj M)) ≫
      R((R d₁ d₂ b)_*[ModuleCat.{u + 1} A]).map
        (D((E d₁ d₂ b)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
            (F d₁ d₂ b).a (BW d₁ d₂ b) (H d₁ d₂ b).a
            (ambient_a_BW d₁ d₂ b)).hom.app M)) := by
  cases b <;>
    dsimp only [EtaleGraphPresentation.functor, Functor.comp_obj] <;>
    simp only [liftInterchange,
      EtaleGraphInterchangeDiagram.ProductRow.First.liftInterchange,
      EtaleGraphInterchangeDiagram.ProductRow.Second.liftInterchange, bridge,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Functor.comp_map, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id, Category.assoc]
  all_goals rfl

-- Keep the interchange algebra abstract, so rewriting never unfolds the pullback maps.
private theorem assemble_lift
    {C₀ C₁ C₁' P C₂ C₂' N N' Y Q Q' : Type*}
    [Category C₀] [Category C₁] [Category C₁'] [Category P]
    [Category C₂] [Category C₂'] [Category N] [Category N']
    [Category Y] [Category Q] [Category Q']
    (Ra : C₀ ⥤ C₁) (Rt : C₀ ⥤ C₁') (Rp : P ⥤ Y) (Rq : Y ⥤ Q)
    (Rr : N ⥤ Q) (Rr' : N' ⥤ Q') (Rc : P ⥤ N) (Rc' : P ⥤ N')
    (Rb : C₁ ⥤ C₂) (Rb' : C₁' ⥤ C₂') (Rh : C₀ ⥤ C₂)
    (Rh' : C₀ ⥤ C₂') (Rg' : Y ⥤ Q')
    (Je : C₁ ⥤ P) (Je' : C₁' ⥤ P) (JE : C₂ ⥤ N) (JE' : C₂' ⥤ N')
    (Jv : C₁' ⥤ C₁) (Jw : C₂' ⥤ C₂) (Jn : N' ⥤ N) (Jk : Q' ⥤ Q)
    (T : Rt ⋙ Jv ≅ Ra) (U : Rh' ⋙ Jw ≅ Rh) (V : Rg' ⋙ Jk ≅ Rq)
    (C : Rp ⋙ Rq ≅ Rc ⋙ Rr) (C' : Rp ⋙ Rg' ≅ Rc' ⋙ Rr')
    (D : Ra ⋙ Rb ≅ Rh) (D' : Rt ⋙ Rb' ≅ Rh')
    (EA : Rb ⋙ JE ≅ Je ⋙ Rc) (EB : Rb' ⋙ JE' ≅ Je' ⋙ Rc')
    (ES : Rb' ⋙ Jw ≅ Jv ⋙ Rb) (EM : Rr' ⋙ Jk ≅ Jn ⋙ Rr)
    (O : Je' ≅ Jv ⋙ Je) (S : Jw ⋙ JE ≅ JE' ⋙ Jn) (L : Rc' ⋙ Jn ≅ Rc)
    (M : C₀)
    (ht : D.hom.app M ≫ U.inv.app M =
      Rb.map (T.inv.app M) ≫ ES.inv.app (Rt.obj M) ≫ Jw.map (D'.hom.app M))
    (hh : EA.inv.app (Jv.obj (Rt.obj M)) ≫ JE.map (ES.inv.app (Rt.obj M)) ≫
        S.hom.app (Rb'.obj (Rt.obj M)) =
      Rc.map (O.inv.app (Rt.obj M)) ≫ L.inv.app (Je'.obj (Rt.obj M)) ≫
        Jn.map (EB.inv.app (Rt.obj M)))
    (hg : C.hom.app (Je'.obj (Rt.obj M)) ≫
        Rr.map (L.inv.app (Je'.obj (Rt.obj M))) ≫
        EM.inv.app (Rc'.obj (Je'.obj (Rt.obj M))) =
      V.inv.app (Rp.obj (Je'.obj (Rt.obj M))) ≫
        Jk.map (C'.hom.app (Je'.obj (Rt.obj M)))) :
    C.hom.app (Je.obj (Ra.obj M)) ≫ Rr.map (EA.inv.app (Ra.obj M)) ≫
        Rr.map (JE.map (D.hom.app M)) ≫ Rr.map (JE.map (U.inv.app M)) ≫
        Rr.map (S.hom.app (Rh'.obj M)) ≫ EM.inv.app (JE'.obj (Rh'.obj M)) =
      Rq.map (Rp.map (Je.map (T.inv.app M))) ≫
        Rq.map (Rp.map (O.inv.app (Rt.obj M))) ≫
        V.inv.app (Rp.obj (Je'.obj (Rt.obj M))) ≫
        Jk.map (C'.hom.app (Je'.obj (Rt.obj M))) ≫
        Jk.map (Rr'.map (EB.inv.app (Rt.obj M))) ≫
        Jk.map (Rr'.map (JE'.map (D'.hom.app M))) := by
  have hnA := EA.inv.naturality (T.inv.app M)
  have hnS := S.hom.naturality (D'.hom.app M)
  have hnC := C.hom.naturality (Je.map (T.inv.app M))
  have hnO := C.hom.naturality (O.inv.app (Rt.obj M))
  have hnD := EM.inv.naturality (JE'.map (D'.hom.app M))
  have hnE := EM.inv.naturality (EB.inv.app (Rt.obj M))
  simp only [Functor.comp_map, Functor.comp_obj] at hnA hnS hnC hnO hnD hnE
  simp only [← Rr.map_comp_assoc]
  rw [← JE.map_comp_assoc, ht]
  simp only [JE.map_comp, Category.assoc]
  rw [← reassoc_of% hnA, hnS, reassoc_of% hh]
  simp only [Rr.map_comp, Category.assoc]
  rw [← reassoc_of% hnC, ← reassoc_of% hnO,
    hnD, reassoc_of% hnE, reassoc_of% hg]

private theorem lift_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (b : Bool) :
    (liftInterchange d₁ d₂ b A).hom ≫ (middle d₁ d₂ b A).hom =
      Functor.whiskerRight (sourceShrink d₁ d₂ b A).hom
        R(((G d₁ d₂ b).a)_*[ModuleCat.{u + 1} A]) ≫
      Functor.whiskerLeft ((d₁.productF d₂).functor A)
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
          (d₁.productG d₂).a (vg d₁ d₂ b) (G d₁ d₂ b).a rfl).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (d₁.productLiftInterchange d₂ A).hom
        D((vg d₁ d₂ b)_!open[ModuleCat.{u + 1} A]) := by
  dsimp only [EtaleGraphPresentation.functor, F₀, Functor.comp_obj]
  let Ra := R(((F d₁ d₂ b).a)_*[ModuleCat.{u + 1} A])
  let Rt := R(((d₁.productF d₂).a)_*[ModuleCat.{u + 1} A])
  let Rp := R(((F d₁ d₂ b).p)_*[ModuleCat.{u + 1} A])
  let Rq := R(((G d₁ d₂ b).a)_*[ModuleCat.{u + 1} A])
  let Rr := R((R d₁ d₂ b)_*[ModuleCat.{u + 1} A])
  let Rr' := R((d₁.productR d₂)_*[ModuleCat.{u + 1} A])
  let Rc := R((BV d₁ d₂ b)_*[ModuleCat.{u + 1} A])
  let Rb := R((BW d₁ d₂ b)_*[ModuleCat.{u + 1} A])
  let Rb' := R((d₁.productBW d₂)_*[ModuleCat.{u + 1} A])
  let Je := D(((F d₁ d₂ b).e)_!open[ModuleCat.{u + 1} A])
  let Je' := D(((d₁.productF d₂).e)_!open[ModuleCat.{u + 1} A])
  let JE := D((E d₁ d₂ b)_!open[ModuleCat.{u + 1} A])
  let JE' := D((d₁.productE d₂)_!open[ModuleCat.{u + 1} A])
  let Jv := D((vf d₁ d₂ b)_!open[ModuleCat.{u + 1} A])
  let Jn := D((n d₁ d₂ b)_!open[ModuleCat.{u + 1} A])
  let Jk := D((vg d₁ d₂ b)_!open[ModuleCat.{u + 1} A])
  let T := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
    (d₁.productF d₂).a (vf d₁ d₂ b) (F d₁ d₂ b).a rfl
  let U := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
    (d₁.productH d₂).a (vh d₁ d₂ b) (H d₁ d₂ b).a rfl
  let V := rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
    (d₁.productG d₂).a (vg d₁ d₂ b) (G d₁ d₂ b).a rfl
  let C := bridge A (F d₁ d₂ b).p (G d₁ d₂ b).a (BV d₁ d₂ b)
    (R d₁ d₂ b) (ambient_BV_R d₁ d₂ b).symm
  let C' := bridge A (d₁.productF d₂).p (d₁.productG d₂).a
    (d₁.productBV d₂) (d₁.productR d₂) (d₁.productBV_productR d₂).symm
  let D := rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
    (F d₁ d₂ b).a (BW d₁ d₂ b) (H d₁ d₂ b).a (ambient_a_BW d₁ d₂ b)
  let D' := rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
    (d₁.productF d₂).a (d₁.productBW d₂) (d₁.productH d₂).a (d₁.productA_productBW d₂)
  let EA := etaleGraphNormalizedProperOpenExchange A (F d₁ d₂ b).e
    (BW d₁ d₂ b) (BV d₁ d₂ b) (E d₁ d₂ b) (ambient_B_square d₁ d₂ b)
  let EB := etaleGraphNormalizedProperOpenExchange A (d₁.productF d₂).e
    (d₁.productBW d₂) (d₁.productBV d₂) (d₁.productE d₂) (d₁.productB_square d₂)
  let s : CommSq (vf d₁ d₂ b) (d₁.productBW d₂) (BW d₁ d₂ b)
      (vh d₁ d₂ b) := ⟨vf_BW d₁ d₂ b⟩
  let ES := etaleGraphNormalizedProperOpenExchange A (vf d₁ d₂ b)
    (d₁.productBW d₂) (BW d₁ d₂ b) (vh d₁ d₂ b) s
  let EM := etaleGraphNormalizedProperOpenExchange A (n d₁ d₂ b)
    (d₁.productR d₂) (R d₁ d₂ b) (vg d₁ d₂ b) (shrink_square d₁ d₂ b)
  let O := open_comp A (vf d₁ d₂ b) (F d₁ d₂ b).e (d₁.productF d₂).e
    (EtaleGraphPresentation.ProductRow.v_j
      d₁.sourcePresentation d₂.sourcePresentation b)
  let S := openRectangle d₁ d₂ b A
  ext M
  have ht := graph_square A (F d₁ d₂ b).a (d₁.productF d₂).a
    (H d₁ d₂ b).a (d₁.productH d₂).a (vf d₁ d₂ b) (vh d₁ d₂ b)
    (BW d₁ d₂ b) (d₁.productBW d₂) rfl rfl (ambient_a_BW d₁ d₂ b)
    (d₁.productA_productBW d₂) s M
  change D.hom.app M ≫ U.inv.app M =
    Rb.map (T.inv.app M) ≫ ES.inv.app (Rt.obj M) ≫
      D((vh d₁ d₂ b)_!open[ModuleCat.{u + 1} A]).map (D'.hom.app M) at ht
  have hh := horizontal_shrink A (vf d₁ d₂ b) (vh d₁ d₂ b)
    (F d₁ d₂ b).e (d₁.productF d₂).e (E d₁ d₂ b) (d₁.productE d₂)
    (n d₁ d₂ b) (BW d₁ d₂ b) (d₁.productBW d₂) (BV d₁ d₂ b)
    (d₁.productBV d₂) (EtaleGraphPresentation.ProductRow.v_j
      d₁.sourcePresentation d₂.sourcePresentation b) (vh_E d₁ d₂ b)
    (productBV_n d₁ d₂ b) s (ambient_B_square d₁ d₂ b) (d₁.productB_square d₂)
    (Rt.obj M)
  change EA.inv.app (Jv.obj (Rt.obj M)) ≫ JE.map (ES.inv.app (Rt.obj M)) ≫
    S.hom.app (Rb'.obj (Rt.obj M)) =
    Rc.map (O.inv.app (Rt.obj M)) ≫
    (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
      (d₁.productBV d₂) (n d₁ d₂ b) (BV d₁ d₂ b) (productBV_n d₁ d₂ b)).inv.app
      (Je'.obj (Rt.obj M)) ≫ Jn.map (EB.inv.app (Rt.obj M)) at hh
  have hg := middle_graph A (F d₁ d₂ b).p (G d₁ d₂ b).a
    (d₁.productG d₂).a (vg d₁ d₂ b) (BV d₁ d₂ b) (d₁.productBV d₂)
    (n d₁ d₂ b) (R d₁ d₂ b) (d₁.productR d₂) rfl (productBV_n d₁ d₂ b)
    (ambient_BV_R d₁ d₂ b).symm (d₁.productBV_productR d₂).symm
    (shrink_square d₁ d₂ b) (Je'.obj (Rt.obj M))
  have hc :
      C.hom.app (Je.obj (Ra.obj M)) ≫ Rr.map (EA.inv.app (Ra.obj M)) ≫
        Rr.map (JE.map (D.hom.app M)) ≫ Rr.map (JE.map (U.inv.app M)) ≫
        Rr.map (S.hom.app (R(((d₁.productH d₂).a)_*[ModuleCat.{u + 1} A]).obj M)) ≫
        EM.inv.app (JE'.obj (R(((d₁.productH d₂).a)_*[ModuleCat.{u + 1} A]).obj M)) =
      Rq.map (Rp.map (Je.map (T.inv.app M))) ≫
        Rq.map (Rp.map (O.inv.app (Rt.obj M))) ≫
        V.inv.app (Rp.obj (Je'.obj (Rt.obj M))) ≫
        Jk.map (C'.hom.app (Je'.obj (Rt.obj M))) ≫
        Jk.map (Rr'.map (EB.inv.app (Rt.obj M))) ≫
        Jk.map (Rr'.map (JE'.map (D'.hom.app M))) := by
    have hgg : C.hom.app (Je'.obj (Rt.obj M)) ≫
        Rr.map ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
          (d₁.productBV d₂) (n d₁ d₂ b) (BV d₁ d₂ b) (productBV_n d₁ d₂ b)).inv.app
          (Je'.obj (Rt.obj M))) ≫
        EM.inv.app (R((d₁.productBV d₂)_*[ModuleCat.{u + 1} A]).obj
          (Je'.obj (Rt.obj M))) =
      V.inv.app (Rp.obj (Je'.obj (Rt.obj M))) ≫
        Jk.map (C'.hom.app (Je'.obj (Rt.obj M))) := by
      simpa only [C, C', bridge, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.map_comp, Category.assoc] using hg
    exact assemble_lift Ra Rt Rp Rq Rr Rr' Rc _ Rb Rb' _ _ _
      Je Je' JE JE' Jv _ Jn Jk T U V C C' D D' EA EB ES EM O S _ M ht hh hgg
  have hO := open_comp_inv A (vf d₁ d₂ b) (F d₁ d₂ b).e (d₁.productF d₂).e
    (EtaleGraphPresentation.ProductRow.v_j
      d₁.sourcePresentation d₂.sourcePresentation b)
  change O.inv = _ at hO
  rw [hO] at hc
  simpa only [EtaleGraphPresentation.functor, Functor.comp_obj,
    Iso.symm_inv,
    C, C', D, D', T, U, V, EA, EB, EM, S, O, Ra, Rt, Rp, Rq, Rr, Rr',
    Je, Je', JE, JE', Jv, Jn, Jk, Rc, Rb, Rb', bridge, open_comp,
    NatTrans.comp_app, lift_formula, middle, sourceShrink,
    EtaleGraphPresentation.ProductRow.shrinkLambda,
    EtaleGraphInterchangeDiagram.productLiftInterchange,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc] using hc

/-- The inverse B exchanges commute with the three supporting-open shrinkings,
up to the explicit mixed-neighborhood boundary. This stops before either Q exchange.
Source: Stacks Project, more-etale.tex, vertical pasting (Tag 0F7C), horizontal
pasting (Tag 0F7D), and the graph-triangle cancellation in Tag 0F7J.
(auxiliary; not a blueprint node).

Proof: form the square with horizontal opens vf and vh and proper vertical maps
productBW and the selected ambient BW. It commutes: compose with the monomorphism
H.e, use BW_e and the equations vf F.e = productF.e and vh H.e = productH.e,
and then the product B square. The identity-top triangle with proper edges
productF.a and F.a pastes vertically above this square to the triangle with
proper edges productH.a and H.a. Vertical exchange pasting and the proper
compositor associativity compare their inverse exchanges. Next compare two horizontal
pastings: the square (vf,productBW,BW,vh)
followed by the ambient B square, and the product B square followed by the
identity-top triangle (id,productBV,BV,n). Their outer squares agree, since
vf F.e = productF.e, vh E = productE n and productBV n = BV.
Horizontal pasting therefore compares the inverse B exchanges.
Finally paste this comparison vertically with the mixed-neighborhood square
(n,productR,R,vg). The relation productBV productR = productF.p productG.a
and its ambient counterpart identify the outer proper edges. Vertical pasting
moves the inverse middle-graph triangle across this rectangle. Substitute these
three equations into liftBoundary, sourceShrink and middleShrink. Naturality
moves factors meeting only at a vertex; the inner exchanges cancel in inverse
pairs. The remaining mixed factors are exactly middleBoundary: the inverse
composite graph triangle, openRectangle, the inverse mixed exchange, and the
open compositor for vg. Open-compositor associativity gives its stated order.
No Q exchange, productSquareInterchange or ambient squareInterchange is used.
All arguments use morphism equalities and pasting, also for empty or identity opens. -/
theorem etaleGraphProductShrinkLift
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (liftBoundary d₁ d₂ second A).hom ≫ (middleBoundary d₁ d₂ second A).hom =
      (inputBoundary d₁ d₂ second A).hom ≫ (productLiftBoundary d₁ d₂ A).hom := by
  let tail : D((vg d₁ d₂ second)_!open[ModuleCat.{u + 1} A]) ⋙
      suffix d₁ d₂ second A ≅ productSuffix d₁ d₂ A :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (vg d₁ d₂ second) (G d₁ d₂ second).e).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (EtaleGraphPresentation.ProductRow.v_j
              (EtaleGraphPresentation.ofCompactification d₁.compactification)
              (EtaleGraphPresentation.ofCompactification d₂.compactification) second)) _
  ext M
  dsimp only [EtaleGraphPresentation.functor, F₀, Functor.comp_obj]
  have h := congr_app (lift_core A d₁ d₂ second) M
  have hh := congrArg (fun z ↦ (suffix d₁ d₂ second A).map z ≫
    tail.hom.app ((d₁.productF₀ d₂ A).obj M)) h
  have hn := tail.hom.naturality ((d₁.productLiftInterchange d₂ A).hom.app M)
  change (suffix d₁ d₂ second A).map
      (D((vg d₁ d₂ second)_!open[ModuleCat.{u + 1} A]).map
        ((d₁.productLiftInterchange d₂ A).hom.app M)) ≫ _ = _ at hn
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc] at hh
  rw [hn] at hh
  simpa only [EtaleGraphPresentation.functor, Functor.comp_obj,
    liftBoundary, middleBoundary, inputBoundary, productLiftBoundary,
    middleShrink, EtaleGraphPresentation.ProductRow.shrinkLambda, tail,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc] using hh

end AlgebraicGeometry.Etale
