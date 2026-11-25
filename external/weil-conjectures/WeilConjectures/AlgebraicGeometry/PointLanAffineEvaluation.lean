/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic

import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts

/-!
# Affine evaluation of the point left Kan extension

Source: Bhatt–Scholze, Lemma 4.2.13(1), proof; RefactorInstruction, Section 4,
Lemma point-eval, first paragraph of proof
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Weak contractibility, expressed by sections of epimorphisms of set sheaves.
Source: Bhatt–Scholze, Section 4.2; RefactorInstruction, Lemma point-eval
(auxiliary; not a blueprint node). -/
def PointLanWeaklyContractible (X : Scheme.{u}) (U : X.ProEt) : Prop :=
  ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
    Epi f → Function.Surjective (f.hom.app (op U))

/-- The actual connected-component quotient, with its quotient topology, bundled as profinite.
The topological structure proofs are the recorded component-map theorem.
Source: Bhatt–Scholze, Lemma 4.2.13(1); RefactorInstruction, Lemma point-eval
(auxiliary; not a blueprint node). -/
def pointLanComponents (X : Scheme.{u}) (U : X.ProEt) (hU : IsAffine U.left)
    (wU : PointLanWeaklyContractible X U) : Profinite.{u} :=
  @Profinite.of (ConnectedComponents U.left) _
    ((proEtale_point_components_maps X).1 U hU wU).1
    ((proEtale_point_components_maps X).1 U hU wU).2.1
    ((proEtale_point_components_maps X).1 U hU wU).2.2

/-- Packaging of the evaluation formula in a specified coefficient category.
A pointwise Kan extension is supplied with its unit, rather than with a choice of colimits.
The normalization on every Kan cocone map specifies the evaluation comparison.
Naturality is simultaneous in coefficient sheaves and in weakly contractible affine objects.
The last clause says exactly that the restriction cone for every finite coproduct is a
product cone, also for an empty index type.
Source: Bhatt–Scholze, Lemma 4.2.13(1); RefactorInstruction, Lemma point-eval
(auxiliary; not a blueprint node). -/
def PointLanAffineEvaluationProperty (X : Scheme.{u}) (C : Type w) [Category.{v} C] :
    Prop :=
  ∃ b : ∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
      (S : Profinite.{u}),
      (U ⟶ (profiniteToProEtOf X).obj S) ≃ (pointLanComponents X U hU wU ⟶ S),
    (∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
      (S T : Profinite.{u}) (g : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S),
      b U hU wU T (f ≫ (profiniteToProEtOf X).map g) = b U hU wU S f ≫ g) ∧
    (∀ (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
      (a : V ⟶ U) (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
      b V hV wV S (a ≫ f) =
        (ConcreteCategory.ofHom
          ⟨a.left.continuous.connectedComponentsMap,
          a.left.continuous.connectedComponentsMap_continuous⟩ :
          pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU) ≫
          b U hU wU S f) ∧
    (∃ e : ∀ (F : Sheaf (coherentTopology Profinite.{u}) C)
        (P : X.ProEtᵒᵖ ⥤ C) (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P),
        (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension →
        ∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
          P.obj (op U) ≅ F.obj.obj (op (pointLanComponents X U hU wU)),
      (∀ (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
        (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
        (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
        (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
        (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
        η.app (op S) ≫ P.map f.op ≫ (e F P η hP U hU wU).hom =
          F.obj.map (b U hU wU S f).op) ∧
      (∀ (F G : Sheaf (coherentTopology Profinite.{u}) C)
        (P Q : X.ProEtᵒᵖ ⥤ C)
        (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
        (θ : G.obj ⟶ (profiniteToProEtOf X).op ⋙ Q)
        (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
        (hQ : (Functor.LeftExtension.mk Q θ).IsPointwiseLeftKanExtension)
        (α : F ⟶ G) (β : P ⟶ Q)
        (_hβ : η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op β = α.hom ≫ θ)
        (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
        (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
        (a : V ⟶ U),
        P.map a.op ≫ β.app (op V) ≫ (e G Q θ hQ V hV wV).hom =
          (e F P η hP U hU wU).hom ≫
            F.obj.map (ConcreteCategory.ofHom
              ⟨a.left.continuous.connectedComponentsMap,
              a.left.continuous.connectedComponentsMap_continuous⟩ :
              pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU).op ≫
            α.hom.app (op (pointLanComponents X V hV wV)))) ∧
    (∀ (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
      (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
      (_ : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
      (I : Type u) [Finite I] (U : I → X.ProEt),
      (∀ i : I, IsAffine (U i).left) →
      (∀ i : I, PointLanWeaklyContractible X (U i)) →
      ∃ c : Cofan U, Nonempty (IsColimit c) ∧
        Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op))))

/-- The connected-component equivalence supplies the comparison maps and their two naturalities.
Source: Bhatt–Scholze, Lemma 4.2.13(1), first paragraph.
(auxiliary; not a blueprint node). -/
private theorem point_lan_affine_evaluation_b (X : Scheme.{u}) :
    ∃ b : ∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
      (S : Profinite.{u}),
      (U ⟶ (profiniteToProEtOf X).obj S) ≃
        (pointLanComponents X U hU wU ⟶ S),
    (∀ (U : X.ProEt) (hU : IsAffine U.left)
      (wU : PointLanWeaklyContractible X U)
      (S T : Profinite.{u}) (g : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S),
      b U hU wU T (f ≫ (profiniteToProEtOf X).map g) =
        b U hU wU S f ≫ g) ∧
    (∀ (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
      (a : V ⟶ U) (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
      b V hV wV S (a ≫ f) =
        (ConcreteCategory.ofHom
          ⟨a.left.continuous.connectedComponentsMap,
          a.left.continuous.connectedComponentsMap_continuous⟩ :
          pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU) ≫
          b U hU wU S f) := by
  classical
  obtain ⟨e, he, ha⟩ := (proEtale_point_components_maps X).2
  let b (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
      (S : Profinite.{u}) : (U ⟶ (profiniteToProEtOf X).obj S) ≃
        (pointLanComponents X U hU wU ⟶ S) :=
    (e U hU wU S).trans
      { toFun := fun f ↦ ConcreteCategory.ofHom f
        invFun := fun f ↦ f.hom.hom
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  refine ⟨b, ?_, ?_⟩
  · intro U hU wU S T g f
    apply ConcreteCategory.hom_injective
    exact he U hU wU S T g f
  · intro U V hU hV wU wV a S f
    apply ConcreteCategory.hom_injective
    exact ha U V hU hV wU wV a S f

set_option backward.isDefEq.respectTransparency false in
private def kanTerminal {A B : Type*} [Category* A] [Category* B]
    (L : A ⥤ B) (U : B) (T : A)
    (b : ∀ S, (U ⟶ L.obj S) ≃ (T ⟶ S))
    (hb : ∀ S S' (g : S ⟶ S') (f : U ⟶ L.obj S),
      b S' (f ≫ L.map g) = b S f ≫ g) :
    IsTerminal (CostructuredArrow.mk ((b T).symm (𝟙 T)).op :
      CostructuredArrow L.op (op U)) := by
  let q := (b T).symm (𝟙 T)
  have hq : b T q = 𝟙 T := (b T).apply_symm_apply _
  refine IsTerminal.ofUniqueHom (fun s ↦
    CostructuredArrow.homMk (b s.left.unop s.hom.unop).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    change q ≫ L.map (b _ s.hom.unop) = s.hom.unop
    apply (b _).injective
    rw [hb, hq, Category.id_comp]
  · intro s m
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    have hm : q ≫ L.map m.left.unop = s.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w m)
    have := congrArg (b s.left.unop) hm
    change m.left.unop = b s.left.unop s.hom.unop
    simpa only [hb, hq, Category.id_comp] using this

set_option backward.isDefEq.respectTransparency false in
private theorem kanEvaluation {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (L : A ⥤ B) (U : B) (T : A)
    (b : ∀ S, (U ⟶ L.obj S) ≃ (T ⟶ S))
    (hb : ∀ S S' (g : S ⟶ S') (f : U ⟶ L.obj S),
      b S' (f ≫ L.map g) = b S f ≫ g)
    (F : Aᵒᵖ ⥤ C) (P : Bᵒᵖ ⥤ C) (η : F ⟶ L.op ⋙ P)
    (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension) :
    ∃ e : P.obj (op U) ≅ F.obj (op T),
      ∀ (S : A) (f : U ⟶ L.obj S),
        η.app (op S) ≫ P.map f.op ≫ e.hom = F.map (b S f).op := by
  let t : CostructuredArrow L.op (op U) :=
    CostructuredArrow.mk ((b T).symm (𝟙 T)).op
  let ht : IsTerminal t := kanTerminal L U T b hb
  let c := (Functor.LeftExtension.mk P η).coconeAt (op U)
  have : IsIso (c.ι.app t) := (hP (op U)).isIso_ι_app_of_isTerminal t ht
  refine ⟨(asIso (c.ι.app t)).symm, ?_⟩
  intro S f
  let s : CostructuredArrow L.op (op U) := CostructuredArrow.mk f.op
  have h := c.w (ht.from s)
  change η.app (op S) ≫ P.map f.op ≫ inv (c.ι.app t) = _
  have hm : (ht.from s).left = (b S f).op := rfl
  change F.map (ht.from s).left ≫ c.ι.app t = η.app (op S) ≫ P.map f.op at h
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hm]

set_option backward.isDefEq.respectTransparency false in
private theorem affineEvaluation (X : Scheme.{u}) (C : Type w) [Category.{v} C] :
    PointLanAffineEvaluationProperty X C := by
  classical
  obtain ⟨b, hb, ha⟩ := point_lan_affine_evaluation_b X
  have hEval (F : Sheaf (coherentTopology Profinite.{u}) C)
      (P : X.ProEtᵒᵖ ⥤ C) (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
      (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U) :=
    kanEvaluation (profiniteToProEtOf X) U (pointLanComponents X U hU wU)
      (b U hU wU) (hb U hU wU) F.obj P η hP
  choose e he using hEval
  refine ⟨b, hb, ha, ⟨e, he, ?_⟩, ?_⟩
  · intro F G P Q η θ hP hQ α β hβ U V hU hV wU wV a
    apply (hP (op U)).hom_ext'
    intro S f
    cases S with | op S =>
      have hβS := congrArg (fun z ↦ z.app (op S)) hβ
      change η.app (op S) ≫ β.app ((profiniteToProEtOf X).op.obj (op S)) =
        α.hom.app (op S) ≫ θ.app (op S) at hβS
      let t : pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU :=
        ConcreteCategory.ofHom ⟨a.left.continuous.connectedComponentsMap,
          a.left.continuous.connectedComponentsMap_continuous⟩
      change η.app (op S) ≫ P.map f ≫ (P.map a.op ≫ β.app (op V) ≫
          (e G Q θ hQ V hV wV).hom) =
        η.app (op S) ≫ P.map f ≫ (e F P η hP U hU wU).hom ≫
          F.obj.map t.op ≫ α.hom.app (op (pointLanComponents X V hV wV))
      calc
        _ = η.app (op S) ≫ P.map (f ≫ a.op) ≫ β.app (op V) ≫
            (e G Q θ hQ V hV wV).hom := by simp only [P.map_comp, Category.assoc]
        _ = α.hom.app (op S) ≫ θ.app (op S) ≫ Q.map (f ≫ a.op) ≫
            (e G Q θ hQ V hV wV).hom := by
          rw [β.naturality_assoc, ← Category.assoc, hβS, Category.assoc]
        _ = α.hom.app (op S) ≫ G.obj.map (b V hV wV S (a ≫ f.unop)).op := by
          rw [← he G Q θ hQ V hV wV S (a ≫ f.unop)]
          rfl
        _ = F.obj.map (b U hU wU S f.unop).op ≫
            F.obj.map t.op ≫ α.hom.app (op (pointLanComponents X V hV wV)) := by
          rw [ha U V hU hV wU wV a S f.unop]
          change α.hom.app (op S) ≫ G.obj.map (t ≫ b U hU wU S f.unop).op = _
          rw [op_comp, G.obj.map_comp, ← Category.assoc, ← α.hom.naturality]
          rw [Category.assoc, ← α.hom.naturality]
        _ = _ := by
          rw [← he F P η hP U hU wU S f.unop]
          simp only [Quiver.Hom.op_unop, Category.assoc]
  · intro F P η hP I _ U hU wU
    exact point_lan_finite_products X C F P η hP I U hU wU

/-- The point left Kan presheaf on a weakly contractible affine is evaluation on its
profinite connected-component quotient. The identifications are canonical, natural in
both arguments, preserve the coefficient operations, and send finite disjoint unions
(including the empty one) to products.

Source: Bhatt–Scholze, Lemma 4.2.13(1), proof, first two sentences;
RefactorInstruction, Section 4, Lemma point-eval, proof, first paragraph
(auxiliary; not a blueprint node).

Proof:
1. Use lem-weil-pbc-proetale-point-components-maps to obtain the profinite component
   quotient and the natural correspondence between maps into X[S] and maps into S.
2. For T = pi_0(U), let q correspond to the identity on T. Every map U → X[S]
   corresponds to a unique map T → S. Thus (T,q) is terminal in the Kan index,
   whose arrows reverse the maps of profinite targets. Its colimit is F(T): the
   cocone maps are F(g), and compatibility forces every cocone to factor uniquely
   through its component at (T,q). This works in all three coefficient categories.
3. Components of a finite disjoint union form the finite coproduct of the component
   spaces. The sheaf condition on the finite jointly surjective coproduct cover gives
   the product cone, also for the empty family. Precomposition gives naturality in U;
   naturality of a sheaf morphism gives naturality in F. All cocone maps and the
   resulting isomorphisms are morphisms of the indicated coefficient category. -/
theorem point_lan_affine_evaluation (X : Scheme.{u}) :
    PointLanAffineEvaluationProperty X (Type (u + 1)) ∧
    PointLanAffineEvaluationProperty X AddCommGrpCat.{u + 1} ∧
    PointLanAffineEvaluationProperty X CommRingCat.{u + 1} := by
  exact ⟨affineEvaluation X _, affineEvaluation X _, affineEvaluation X _⟩

end AlgebraicGeometry.ProEtale
