/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkWords
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Shrinking the final Q exchange

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

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private def openC
    (A : Type (u + 1)) [CommRing A] {I J K : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ K) (c : I ⟶ K)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] (h : a ≫ b = c) :=
  mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h.symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b

private theorem openC_rfl
    (A : Type (u + 1)) [CommRing A] {I J K : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ K) [IsOpenImmersion a] [IsOpenImmersion b] :
    openC A a b (a ≫ b) rfl =
      mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b := by
  simp only [openC, mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_trans]

private theorem openC_inv
    (A : Type (u + 1)) [CommRing A] {I J K : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ K) (c : I ⟶ K)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] (h : a ≫ b = c) :
    (openC A a b c h).inv =
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b).inv ≫
        (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).hom := by
  subst c
  rfl

private theorem openC_assoc_inv
    (A : Type (u + 1)) [CommRing A] {I J K T : Scheme.{u}}
    (a : I ⟶ J) (b : J ⟶ K) (e : K ⟶ T)
    (ab : I ⟶ K) (be : J ⟶ T) (w : I ⟶ T)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion e]
    [IsOpenImmersion ab] [IsOpenImmersion be] [IsOpenImmersion w]
    (hab : a ≫ b = ab) (hbe : b ≫ e = be) (hw : ab ≫ e = w) (hw' : a ≫ be = w)
    (M : DerivedCategoryModule A I) :
    D((e)_!open[ModuleCat.{u + 1} A]).map ((openC A a b ab hab).inv.app M) ≫
        (openC A ab e w hw).inv.app M =
      (openC A b e be hbe).inv.app (D((a)_!open[ModuleCat.{u + 1} A]).obj M) ≫
        (openC A a be w hw').inv.app M := by
  have h := (unboundedFormalism A).shComp'_assoc_inv_app a b e ab be w
    hab hbe hw hw' M
  simp_rw [unbounded_sh_comp] at h
  simpa only [openC, unboundedFormalism] using h

-- The two open triples have the same composite, including equality transports.
private theorem open_rectangle_tail
    (A : Type (u + 1)) [CommRing A]
    {I H V N P : Scheme.{u}}
    (v : I ⟶ H) (e : H ⟶ N) (t : I ⟶ V) (n : V ⟶ N) (k : N ⟶ P)
    (h : H ⟶ P) (l : V ⟶ P) (w : I ⟶ P)
    [IsOpenImmersion v] [IsOpenImmersion e] [IsOpenImmersion t]
    [IsOpenImmersion n] [IsOpenImmersion k] [IsOpenImmersion h]
    [IsOpenImmersion l] [IsOpenImmersion w]
    (hve : v ≫ e = t ≫ n) (hek : e ≫ k = h) (hnk : n ≫ k = l)
    (hvh : v ≫ h = w) (htl : t ≫ l = w) (M : DerivedCategoryModule A I) :
    D((k)_!open[ModuleCat.{u + 1} A]).map
        (((openC A v e (t ≫ n) hve).symm ≪≫ openC A t n (t ≫ n) rfl).hom.app M) ≫
        (openC A n k l hnk).inv.app (D((t)_!open[ModuleCat.{u + 1} A]).obj M) ≫
        (openC A t l w htl).inv.app M =
      (openC A e k h hek).inv.app (D((v)_!open[ModuleCat.{u + 1} A]).obj M) ≫
        (openC A v h w hvh).inv.app M := by
  have hm : (t ≫ n) ≫ k = w := by rw [Category.assoc, hnk, htl]
  have h₁ := openC_assoc_inv A v e k (t ≫ n) h w hve hek hm hvh M
  have h₂ := openC_assoc_inv A t n k (t ≫ n) l w rfl hnk hm htl M
  rw [← h₂]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    ← Category.assoc, ← Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  exact h₁

-- Project the law once, before making the selected family locally irreducible.
private theorem normalized_horizontal
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V V' W Z Z' : Scheme.{u}}
    (k : U ⟶ V) (l : V ⟶ V') (i : W ⟶ Z) (j : Z ⟶ Z')
    (r : U ⟶ W) (p : V ⟶ Z) (q : V' ⟶ Z')
    [IsProper r] [IsProper p] [IsProper q]
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    (s₁ : CommSq k r p i) (s₂ : CommSq l p q j) (M : DerivedCategoryModule A U) :
    (etaleGraphNormalizedProperOpenExchange A (k ≫ l) r q (i ≫ j)
      (s₁.horiz_comp s₂)).hom.app M =
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j).hom.app
          (R((r)_*[ModuleCat.{u + 1} A]).obj M) ≫
        D((j)_!open[ModuleCat.{u + 1} A]).map
          ((etaleGraphNormalizedProperOpenExchange A k r p i s₁).hom.app M) ≫
        (etaleGraphNormalizedProperOpenExchange A l p q j s₂).hom.app
          (D((k)_!open[ModuleCat.{u + 1} A]).obj M) ≫
        R((q)_*[ModuleCat.{u + 1} A]).map
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) k l).inv.app M) := by
  simpa only [etaleGraphNormalizedProperOpenExchange] using
    (Classical.choose_spec (Classical.choose_spec (etaleProperOpenExchangeCube A))).2.2.2.2.1
      k l i j r p q s₁ s₂ M

attribute [local irreducible] etaleGraphNormalizedProperOpenExchange

private theorem exchange_rectangle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {I H V N B G P T : Scheme.{u}}
    (v : I ⟶ H) (e : H ⟶ N) (t : I ⟶ V) (n : V ⟶ N) (k : N ⟶ P)
    (h : H ⟶ P) (l : V ⟶ P) (w : I ⟶ P)
    (r : V ⟶ B) (q : N ⟶ G) (p : P ⟶ T)
    (b : B ⟶ G) (j : G ⟶ T) (j' : B ⟶ T)
    [IsOpenImmersion v] [IsOpenImmersion e] [IsOpenImmersion t]
    [IsOpenImmersion n] [IsOpenImmersion k] [IsOpenImmersion h]
    [IsOpenImmersion l] [IsOpenImmersion w] [IsOpenImmersion b]
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsProper r] [IsProper q] [IsProper p]
    (hve : v ≫ e = t ≫ n) (hek : e ≫ k = h) (hnk : n ≫ k = l)
    (hvh : v ≫ h = w) (htl : t ≫ l = w) (hbj : b ≫ j = j')
    (s₁ : CommSq n r q b) (s₂ : CommSq k q p j) (s : CommSq l r p j')
    (M : DerivedCategoryModule A I) (S : DerivedCategoryModule A H)
    (δ : S ⟶ D((v)_!open[ModuleCat.{u + 1} A]).obj M) :
    (etaleGraphNormalizedProperOpenExchange A k q p j s₂).hom.app
        (D((e)_!open[ModuleCat.{u + 1} A]).obj S) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        ((openC A e k h hek).inv.app S ≫
          D((h)_!open[ModuleCat.{u + 1} A]).map δ ≫
          (openC A v h w hvh).inv.app M) =
    D((j)_!open[ModuleCat.{u + 1} A]).map
        (R((q)_*[ModuleCat.{u + 1} A]).map
            (D((e)_!open[ModuleCat.{u + 1} A]).map δ ≫
              (((openC A v e (t ≫ n) hve).symm ≪≫
                openC A t n (t ≫ n) rfl).hom.app M)) ≫
          (etaleGraphNormalizedProperOpenExchange A n r q b s₁).inv.app
            (D((t)_!open[ModuleCat.{u + 1} A]).obj M)) ≫
      (openC A b j j' hbj).inv.app
        (R((r)_*[ModuleCat.{u + 1} A]).obj
          (D((t)_!open[ModuleCat.{u + 1} A]).obj M)) ≫
      (etaleGraphNormalizedProperOpenExchange A l r p j' s).hom.app
        (D((t)_!open[ModuleCat.{u + 1} A]).obj M) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map ((openC A t l w htl).inv.app M) := by
  subst l
  subst j'
  have ho := normalized_horizontal A n k b j r q p s₁ s₂
    (D((t)_!open[ModuleCat.{u + 1} A]).obj M)
  have ho' : (etaleGraphNormalizedProperOpenExchange A (n ≫ k) r p (b ≫ j) s).hom.app
      (D((t)_!open[ModuleCat.{u + 1} A]).obj M) =
    (openC A b j (b ≫ j) rfl).hom.app _ ≫
      D((j)_!open[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A n r q b s₁).hom.app _) ≫
      (etaleGraphNormalizedProperOpenExchange A k q p j s₂).hom.app _ ≫
      R((p)_*[ModuleCat.{u + 1} A]).map
        ((openC A n k (n ≫ k) rfl).inv.app _) := by
    simpa only [openC_rfl] using ho
  rw [ho']
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id]
  erw [Category.comp_id]
  have hn := (etaleGraphNormalizedProperOpenExchange A k q p j s₂).hom.naturality
    (D((e)_!open[ModuleCat.{u + 1} A]).map δ ≫
      (((openC A v e (t ≫ n) hve).symm ≪≫ openC A t n (t ≫ n) rfl).hom.app M))
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  have ht := open_rectangle_tail A v e t n k h (n ≫ k) w hve hek rfl hvh htl M
  have hn' := (openC A e k h hek).inv.naturality δ
  simp only [Functor.comp_map] at hn'
  have hi :
      D((k)_!open[ModuleCat.{u + 1} A]).map
          (D((e)_!open[ModuleCat.{u + 1} A]).map δ ≫
            (((openC A v e (t ≫ n) hve).symm ≪≫
              openC A t n (t ≫ n) rfl).hom.app M)) ≫
          (openC A n k (n ≫ k) rfl).inv.app
            (D((t)_!open[ModuleCat.{u + 1} A]).obj M) ≫
          (openC A t (n ≫ k) w htl).inv.app M =
        (openC A e k h hek).inv.app S ≫ D((h)_!open[ModuleCat.{u + 1} A]).map δ ≫
          (openC A v h w hvh).inv.app M := by
    rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc, hn']
    simp only [Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ (etaleGraphNormalizedProperOpenExchange A k q p j s₂).hom.app
      (D((e)_!open[ModuleCat.{u + 1} A]).obj S) ≫
      R((p)_*[ModuleCat.{u + 1} A]).map z) hi.symm

-- Do naturality algebra before instantiating it with the large geometric functors.
private theorem finish_with_compositor
    {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ D} {Q : D ⥤ E} {T : C ⥤ E} (c : P ⋙ Q ≅ T)
    {S₀ S₁ S₂ S₃ : C} {B : D} {a : B ⟶ P.obj S₀}
    {b : S₀ ⟶ S₁} {d : S₁ ⟶ S₂} {e : S₂ ⟶ S₃} {z : B ⟶ P.obj S₃}
    (h : a ≫ P.map (b ≫ d ≫ e) = z) :
    Q.map a ≫ Q.map (P.map b) ≫ c.hom.app S₁ ≫ T.map d ≫ T.map e =
      Q.map z ≫ c.hom.app S₃ := by
  rw [← c.hom.naturality_assoc, ← c.hom.naturality]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun m ↦ Q.map m ≫ c.hom.app S₃) h

attribute [local irreducible] openC
  EtaleGraphInterchangeDiagram.productE EtaleGraphInterchangeDiagram.productK
  EtaleGraphInterchangeDiagram.productP EtaleGraphInterchangeDiagram.productR

open EtaleGraphInterchangeDiagram.ProductShrink

private theorem square_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool)
    (M : DerivedCategoryModule A X) :
    (squareInterchange d₁ d₂ second A).hom.app M =
      R(((d₁.productG d₂).p)_*[ModuleCat.{u + 1} A]).map
        ((etaleGraphNormalizedProperOpenExchange A (K d₁ d₂ second)
          (R d₁ d₂ second) (d₁.productP d₂) (G d₁ d₂ second).e
          ⟨(R_e d₁ d₂ second).symm⟩).hom.app
          (D((E d₁ d₂ second)_!open[ModuleCat.{u + 1} A]).obj
            (R(((H d₁ d₂ second).a)_*[ModuleCat.{u + 1} A]).obj M))) ≫
        R(((d₁.productG d₂).p)_*[ModuleCat.{u + 1} A]).map
          (R((d₁.productP d₂)_*[ModuleCat.{u + 1} A]).map
            ((openC A (E d₁ d₂ second) (K d₁ d₂ second) (H d₁ d₂ second).e
              (E_K d₁ d₂ second)).inv.app
              (R(((H d₁ d₂ second).a)_*[ModuleCat.{u + 1} A]).obj M))) ≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
          (d₁.productP d₂) (d₁.productG d₂).p (d₁.productH d₂).p
          (d₁.productP_productQ d₂)).hom.app
          (D(((H d₁ d₂ second).e)_!open[ModuleCat.{u + 1} A]).obj
            (R(((H d₁ d₂ second).a)_*[ModuleCat.{u + 1} A]).obj M)) := by
  cases second <;>
    dsimp only [squareInterchange] <;>
    simp only [EtaleGraphInterchangeDiagram.ProductRow.First.squareInterchange,
      EtaleGraphInterchangeDiagram.ProductRow.Second.squareInterchange,
      openC_inv, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Functor.comp_map, Functor.map_comp,
      Category.id_comp, Category.comp_id, Category.assoc]
  all_goals
    erw [Category.id_comp]
    rfl

/-- The final Q exchange commutes with the mixed-neighborhood support shrink.
This assertion involves no source presentation or inverse B exchange.
Source: Stacks Project, more-etale.tex, horizontal exchange pasting (Tag 0F7D),
and the final A--F comparison of Tag 0F7J.
(auxiliary; not a blueprint node).

Proof: the square with top n, bottom vg and proper edges productR,R commutes
by n_R. Paste it horizontally before the ambient Q square. The outer top is
n K = productK, and the outer bottom is vg G.e = productG.e. Horizontal
pasting for the normalized family therefore expresses the product Q exchange
as the mixed exchange followed by the ambient Q exchange, with the canonical
open compositors at both ends. In middleBoundary the mixed exchange occurs
inversely, so these two factors cancel. Move the composite graph triangle
past the ambient Q exchange by its naturality. The two routes through the
three open maps vh,E,K are the same as those through productE,n,K by vh_E,
and E K = H.e and productE productK = productH.e. Associativity of the open
compositors identifies their composites with the open part of compositeShrink.
The final proper compositor is the same in both paths, and its naturality moves
it past the graph triangle. This gives squareInterchange followed by the
composite shrink on one side, and middleBoundary followed by the product
squareInterchange on the other. The source graph and B square never enter;
the identity and empty-open cases use the very same pasting and unit equations. -/
theorem etaleGraphProductShrinkSquare
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d₁ d₂ : EtaleGraphInterchangeDiagram f g) (second : Bool) :
    (squareInterchange d₁ d₂ second A).hom ≫ (compositeShrink d₁ d₂ second A).hom =
      (middleBoundary d₁ d₂ second A).hom ≫ (d₁.productSquareInterchange d₂ A).hom := by
  apply NatTrans.ext
  funext M
  have hr := exchange_rectangle A
    (vh d₁ d₂ second) (E d₁ d₂ second) (d₁.productE d₂) (n d₁ d₂ second)
    (K d₁ d₂ second) (H d₁ d₂ second).e (d₁.productK d₂) (d₁.productH d₂).e
    (d₁.productR d₂) (R d₁ d₂ second) (d₁.productP d₂)
    (vg d₁ d₂ second) (G d₁ d₂ second).e (d₁.productG d₂).e
    (vh_E d₁ d₂ second) (E_K d₁ d₂ second) (n_K d₁ d₂ second)
    (EtaleGraphPresentation.ProductRow.v_j
      d₁.compositePresentation d₂.compositePresentation second)
    (d₁.productE_productK d₂)
    (EtaleGraphPresentation.ProductRow.v_j
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification) second)
    (shrink_square d₁ d₂ second) ⟨(R_e d₁ d₂ second).symm⟩ (d₁.product_square d₂)
    (R(((d₁.productH d₂).a)_*[ModuleCat.{u + 1} A]).obj M)
    (R(((H d₁ d₂ second).a)_*[ModuleCat.{u + 1} A]).obj M)
    ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A
      (d₁.productH d₂).a (vh d₁ d₂ second) (H d₁ d₂ second).a rfl).inv.app M)
  let C := rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
    (d₁.productP d₂) (d₁.productG d₂).p (d₁.productH d₂).p
    (d₁.productP_productQ d₂)
  have hc := finish_with_compositor C hr
  simp only [NatTrans.comp_app, square_component]
  simp only [compositeShrink, EtaleGraphPresentation.ProductRow.shrinkLambda,
    middleBoundary, middle, openRectangle,
    EtaleGraphInterchangeDiagram.productSquareInterchange,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  simpa only [C, openC_inv, openC_rfl, Iso.trans_hom, Iso.symm_hom, Iso.refl_trans,
    Iso.refl_hom, NatTrans.id_app,
    NatTrans.comp_app, Functor.map_comp, Functor.map_id, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc] using hc

end AlgebraicGeometry.Etale
