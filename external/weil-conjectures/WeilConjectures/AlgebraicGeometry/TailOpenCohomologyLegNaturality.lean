/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TailOpenCohomologyArrowLaws
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Restricted cohomology leg naturality

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
private theorem openSquareCoefficient_composition
    {X Y Z X' Y' Z' : Scheme.{u}}
    (f : Y ⟶ X) (k : Z ⟶ Y) (a : X' ⟶ X) (b : Y' ⟶ Y) (d : Z' ⟶ Z)
    (g : Y' ⟶ X') (l : Z' ⟶ Y')
    (h₁ : b ≫ f = g ≫ a) (h₂ : d ≫ k = l ≫ b)
    (q : Z ⟶ X) (r : Z' ⟶ X') (hq : q = k ≫ f) (hr : r = l ≫ g)
    (h : d ≫ q = r ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (ψ : (upperStar AddCommGrpCat.{u + 1} k).obj G ⟶ H) :
    openSquareCoefficient q a d r h F H
      ((upperStarComp AddCommGrpCat.{u + 1} k f q hq).hom.app F ≫
        (upperStar AddCommGrpCat.{u + 1} k).map φ ≫ ψ) =
    (upperStarComp AddCommGrpCat.{u + 1} l g r hr).hom.app
        ((upperStar AddCommGrpCat.{u + 1} a).obj F) ≫
      (upperStar AddCommGrpCat.{u + 1} l).map
        (openSquareCoefficient f a b g h₁ F G φ) ≫
      openSquareCoefficient k b d l h₂ G H ψ := by
  cases hq
  cases hr
  have hp := congrArg (fun t => t.app F)
    (squareUpperStarIso_paste_vert_hom AddCommGrpCat.{u + 1}
      (CommSq.mk h₂) (CommSq.mk h₁) (CommSq.mk h))
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, TwoSquare.vComp_app, Functor.comp_obj] at hp
  change (squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h)).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} d).map
        ((upperStarComp AddCommGrpCat.{u + 1} k f).hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} k).map φ ≫ ψ) = _
  rw [hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  unfold openSquareCoefficient
  change _ = (upperStarComp AddCommGrpCat.{u + 1} l g).hom.app _ ≫
    (upperStar AddCommGrpCat.{u + 1} l).map
      ((squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h₁)).hom.app F ≫
        (upperStar AddCommGrpCat.{u + 1} b).map φ) ≫
      (squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h₂)).hom.app G ≫
        (upperStar AddCommGrpCat.{u + 1} d).map ψ
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (squareUpperStarIso AddCommGrpCat.{u + 1} (CommSq.mk h₂)).hom.naturality φ
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]


private theorem cohomologyMap_transported_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : c = a ≫ b)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (l : (upperStar AddCommGrpCat.{u + 1} b).obj G ⟶ F)
    (k : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ K)
    (q : ℕ) (x : Sheaf.H G q) :
    Sheaf.H.map k q (cohomologyMap a F q (Sheaf.H.map l q (cohomologyMap b G q x))) =
      Sheaf.H.map (((upperStarComp AddCommGrpCat.{u + 1} a b c hc).hom.app G) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map l ≫ k) q (cohomologyMap c G q x) := by
  let y := cohomologyMap c G q x
  let m := (upperStar AddCommGrpCat.{u + 1} a).map l
  let e := upperStarComp AddCommGrpCat.{u + 1} a b c hc
  calc
    _ = Sheaf.H.map k q (Sheaf.H.map m q
        (cohomologyMap a ((upperStar AddCommGrpCat.{u + 1} b).obj G) q
          (cohomologyMap b G q x))) :=
      congrArg (Sheaf.H.map k q) (cohomologyMap_map a q l (cohomologyMap b G q x))
    _ = Sheaf.H.map k q (Sheaf.H.map m q (Sheaf.H.map (e.hom.app G) q y)) :=
      congrArg (fun z ↦ Sheaf.H.map k q (Sheaf.H.map m q z))
        (by
          subst c
          exact (cohomologyPullbackFunctorial a b G q).2.1 x)
    _ = Sheaf.H.map (m ≫ k) q (Sheaf.H.map (e.hom.app G) q y) :=
      (Sheaf.H.map_comp_apply m k _).symm
    _ = _ := (Sheaf.H.map_comp_apply (e.hom.app G) (m ≫ k) y).symm


/-- Canonical cohomology leg from a stage open to the limit open.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-leg-naturality). -/
noncomputable def tailOpenCohomologyCoconeLeg {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (n : ℕ) (j : Set.Ici i₀) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) n) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailLimitOpenMap D c g₀ W j) _ n) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (c.π.app (op j.val)) (tailStageOpen D g₀ W j).ι
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (tailLimitOpenMap D c g₀ W j)
        (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
        ((eG j.val).inv ≫ L.ι.app j.val)) n)

set_option backward.isDefEq.respectTransparency false in
/-- The restricted cohomology legs commute with the restricted transitions.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-leg-naturality).

Proof: Precompose the cocone equation G.map f; L_k = L_j by eG_j.inv and substitute hG.
Cancel the inverse isomorphisms to obtain the original coefficient leg equation.
Restrict it along the limit-open inclusion. The projection square and transition square
paste to the projection square at j. Vertical pasting of inverse-image square comparisons
and naturality in the coefficient transition identify the restricted coefficient equation
with the composite of the restricted transition and restricted leg at k. The scheme
projections compose because both agree after the stage-open inclusion, by c.w.
Apply cohomology pullback composition, coefficient naturality and Sheaf.H.map composition
to this coefficient equation. The displayed naturality equality follows. The argument
uses arbitrary cocones, and includes empty opens and zero coefficients. -/
theorem tailOpenCohomologyCoconeLeg_naturality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (n : ℕ)
    (j k : Set.Ici i₀) (f : j ⟶ k) :
    tailOpenCohomologyArrow D g₀ W F φ n f ≫
      tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n k =
      tailOpenCohomologyCoconeLeg D c g₀ W F G eG L n j := by
  let f₀ : j.val ⟶ k.val := homOfLE (show j.val ≤ k.val from f.le)
  have hr : tailLimitOpenMap D c g₀ W j =
      tailLimitOpenMap D c g₀ W k ≫ tailStageOpenMap D g₀ W f := by
    apply (cancel_mono (tailStageOpen D g₀ W j).ι).1
    rw [Category.assoc]
    simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc]
    simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
    exact congrArg (fun t => ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ t)
      (c.w f₀.op).symm
  have h₁ : (tailStageOpen D g₀ W k).ι ≫ D.map f₀.op =
      tailStageOpenMap D g₀ W f ≫ (tailStageOpen D g₀ W j).ι := by
    simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
    rfl
  have h₂ : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ c.π.app (op k.val) =
      tailLimitOpenMap D c g₀ W k ≫ (tailStageOpen D g₀ W k).ι := by
    simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
  have h₃ : ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ c.π.app (op j.val) =
      tailLimitOpenMap D c g₀ W j ≫ (tailStageOpen D g₀ W j).ι := by
    simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
  have he : (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
      (D.map f₀.op) (c.π.app (op j.val)) (c.w f₀.op).symm).hom.app (F j.val) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op k.val))).map (φ f₀) ≫
        ((eG k.val).inv ≫ L.ι.app k.val) = (eG j.val).inv ≫ L.ι.app j.val := by
    have hw := congrArg (fun t => (eG j.val).inv ≫ t) (L.w f₀)
    rw [hG] at hw
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hw
  have hp := openSquareCoefficient_composition (D.map f₀.op) (c.π.app (op k.val))
    (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
    ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
    (tailStageOpenMap D g₀ W f) (tailLimitOpenMap D c g₀ W k) h₁ h₂
    (c.π.app (op j.val)) (tailLimitOpenMap D c g₀ W j)
    (c.w f₀.op).symm hr h₃ (F j.val) (F k.val) L.pt (φ f₀)
    ((eG k.val).inv ≫ L.ι.app k.val)
  rw [he] at hp
  ext x
  change Sheaf.H.map _ n (cohomologyMap (tailLimitOpenMap D c g₀ W k) _ n
    (Sheaf.H.map _ n (cohomologyMap (tailStageOpenMap D g₀ W f) _ n x))) = _
  rw [cohomologyMap_transported_comp _ _ _ hr]
  rw [← hp]
  rfl

end AlgebraicGeometry.Etale
