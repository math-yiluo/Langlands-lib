/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone
import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem
import WeilConjectures.AlgebraicGeometry.EtaleOpenSquareDiagramIdentity
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Restricted cohomology arrow laws

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- Canonical cohomology transition on the restricted stage opens.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-tail-open-cohomology-arrow-laws). -/
noncomputable def tailOpenCohomologyArrow {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (n : ℕ) {j k : Set.Ici i₀} (f : j ⟶ k) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) n) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W k).ι).obj (F k.val)) n) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailStageOpenMap D g₀ W f) _ n) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
        (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
        (tailStageOpenMap D g₀ W f)
        (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
        (F j.val) (F k.val)
        (φ (homOfLE (show j.val ≤ k.val from f.le)))) n)

private theorem functor_transport_map
    {α C D : Type*} [Category C] [Category D]
    (P : α → C ⥤ D) (K : D ⥤ AddCommGrpCat.{u + 1}) (F : C) {A : Type*}
    (m : ∀ a, A → K.obj ((P a).obj F)) (a b : α) (h : a = b) (x : A) :
    K.map ((eqToIso (congrArg P h)).hom.app F) (m a x) = m b x := by
  subst b
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem cohomology_identity_transport {X : Scheme.{u}} (f : X ⟶ X)
    (hf : f = 𝟙 X) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map
      ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app F ≫
        (upperStarId AddCommGrpCat.{u + 1} X).hom.app F) n
      (cohomologyMap f F n x) = x := by
  rw [Sheaf.H.map_comp_apply]
  have ht := functor_transport_map (upperStar AddCommGrpCat.{u + 1})
    (Sheaf.functorH X.smallEtaleTopology n) F
    (fun f x ↦ cohomologyMap f F n x) f (𝟙 X) hf x
  change Sheaf.H.map
    ((eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) hf)).hom.app F) n
    (cohomologyMap f F n x) = cohomologyMap (𝟙 X) F n x at ht
  exact (congrArg (Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) n)
    ht).trans ((cohomologyPullbackFunctorial (𝟙 X) (𝟙 X) F n).2.2 x)

private theorem cohomology_composition_transport {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (t : A ⟶ C) (h : t = a ≫ b)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b t h).hom.app F) n
      (cohomologyMap t F n x) = cohomologyMap a _ n (cohomologyMap b F n x) := by
  subst t
  exact ((cohomologyPullbackFunctorial a b F n).2.1 x).symm

set_option backward.isDefEq.respectTransparency false in
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
  have hp := congrArg (fun t ↦ t.app F)
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



private theorem coefficientCohomology_composition {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (t : A ⟶ C) (h : t = a ≫ b)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1})
    (α : (upperStar AddCommGrpCat.{u + 1} b).obj F ⟶ G)
    (β : (upperStar AddCommGrpCat.{u + 1} a).obj G ⟶ H) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b t h).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} a).map α ≫ β) n (cohomologyMap t F n x) =
      Sheaf.H.map β n (cohomologyMap a G n (Sheaf.H.map α n (cohomologyMap b F n x))) := by
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  exact (congrArg (fun y ↦ Sheaf.H.map β n
    (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} a).map α) n y))
    (cohomology_composition_transport a b t h F n x)).trans
    (congrArg (Sheaf.H.map β n) (cohomologyMap_map a n α (cohomologyMap b F n x)).symm)

/-- Restricted cohomology transitions preserve identities and composition.
Source: Stacks Project, Tags 09YQ (coherent systems) and 01F7 (functoriality).
(blueprint: lem-weil-pbc-tail-open-cohomology-arrow-laws).

Proof: Cancel the monomorphic stage-open inclusions to prove that tailStageOpenMap
preserves identities and reverses composites. Substitute hidentity in the identity
coefficient square. The two inverse-image unit laws cancel the original identity
comparison, leaving the canonical identity comparison on the restricted sheaf.
Cohomology pullback along identity followed by this comparison is the identity.
For composition substitute hcomposition, expand openSquareCoefficient, and use
naturality to move the first coefficient transition across the second square comparison.
Vertical pasting of inverse-image square isomorphisms identifies the comparisons with
that of the composite square. Cohomology pullback composition, naturality in the
coefficient sheaf, and functoriality of Sheaf.H.map then give the displayed composition.
No cocone, colimit, continuity or vanishing assertion is used. Empty opens and zero
coefficients are covered by the same functoriality equations. -/
theorem tailOpenCohomologyArrow_laws
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (n : ℕ) :
    (∀ j : Set.Ici i₀, tailOpenCohomologyArrow D g₀ W F φ n (𝟙 j) = 𝟙 _) ∧
    (∀ (j k l : Set.Ici i₀) (f : j ⟶ k) (g : k ⟶ l),
      tailOpenCohomologyArrow D g₀ W F φ n (f ≫ g) =
        tailOpenCohomologyArrow D g₀ W F φ n f ≫
          tailOpenCohomologyArrow D g₀ W F φ n g) := by
  let E := tailOpenDiagram D g₀ W
  let F' := tailOpenSheaf D g₀ W F
  let ψ := @tailOpenCoefficient I _ D X i₀ g₀ W F φ
  have hid : ∀ j : Set.Ici i₀, ψ (𝟙 j) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))).hom.app
        (F' j) ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app (F' j) := by
    intro j
    exact openSquareCoefficient_diagram_identity D E
      Subtype.val (fun j ↦ (tailStageOpen D g₀ W j).ι) F φ hidentity
      (fun j ↦ by
        simp only [E, tailOpenDiagram, tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
      F' (fun _ ↦ rfl) (fun j ↦ ψ (𝟙 j)) (fun _ ↦ HEq.rfl) j
  have hcomp : ∀ (j k l : Set.Ici i₀) (f : j ⟶ k) (g : k ⟶ l),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (E.map g.op) (E.map f.op)
          (E.map (f ≫ g).op) (E.map_comp g.op f.op)).hom.app (F' j) ≫
        (upperStar AddCommGrpCat.{u + 1} (E.map g.op)).map (ψ f) ≫ ψ g := by
    intro j k l f g
    dsimp only [ψ]
    unfold tailOpenCoefficient
    rw [show homOfLE (show j.val ≤ l.val from (f ≫ g).le) =
      homOfLE (show j.val ≤ k.val from f.le) ≫
        homOfLE (show k.val ≤ l.val from g.le) from Subsingleton.elim _ _]
    simp only [hcomposition]
    exact openSquareCoefficient_composition _ _ _ _ _ _ _ _ _ _ _
      (D.map_comp _ _) (E.map_comp g.op f.op) _ _ _ _ _ _
  constructor
  · intro j
    ext x
    change Sheaf.H.map (ψ (𝟙 j)) n (cohomologyMap (E.map (𝟙 (op j))) (F' j) n x) = x
    rw [hid]
    exact cohomology_identity_transport _ (E.map_id (op j)) (F' j) n x
  · intro j k l f g
    ext x
    change Sheaf.H.map (ψ (f ≫ g)) n
      (cohomologyMap (E.map (f ≫ g).op) (F' j) n x) =
        Sheaf.H.map (ψ g) n (cohomologyMap (E.map g.op) (F' k) n
          (Sheaf.H.map (ψ f) n (cohomologyMap (E.map f.op) (F' j) n x)))
    rw [hcomp]
    exact coefficientCohomology_composition (E.map g.op) (E.map f.op)
      (E.map (f ≫ g).op) (E.map_comp g.op f.op) (F' j) (F' k) (F' l) (ψ f) (ψ g) n x

end AlgebraicGeometry.Etale
