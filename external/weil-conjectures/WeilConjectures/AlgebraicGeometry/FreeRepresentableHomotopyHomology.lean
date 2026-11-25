/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.SingleHomotopyPresheafHomology
import WeilConjectures.CategoryTheory.MapExtendHomology

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

/-- The presheaf of homotopy classes from free representables to the integer extension
of a nonnegative complex of abelian sheaves. It is constructed by preadditive Yoneda. 
(blueprint: lem-weil-pbc-free-representable-homotopy-homology)
-/
def freeRepresentableHomotopyPresheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v} ⋙ CochainComplex.singleFunctor _ 0 ⋙
    HomotopyCategory.quotient _ (.up ℤ)).op ⋙
      preadditiveYoneda.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((K.extend ComplexShape.embeddingUpNat)⟦(q : ℤ)⟧))

private abbrev freeRepresentableSheafFunctor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v}

open Opposite in
private def freeSectionsEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeRepresentableSheafFunctor J).obj X ⟶ F) ≃+ F.obj.obj (op X) := by
  let e := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) F.obj).trans
      yonedaEquiv)
  refine { toEquiv := e, map_add' := ?_ }
  intro a b
  dsimp [e, Adjunction.homEquiv, yonedaEquiv]

open Opposite in
private lemma freeSectionsEquiv_postcomp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C)
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (a : (freeRepresentableSheafFunctor J).obj X ⟶ F) :
    freeSectionsEquiv J X G (a ≫ f) =
      f.hom.app (op X) (freeSectionsEquiv J X F a) := by
  change yonedaEquiv
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) G.obj)
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ G) (a ≫ f))) =
    f.hom.app (op X) (yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) F.obj)
        (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F) a)))
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

open Opposite in
private lemma freeSectionsEquiv_precomp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] {X Y : C} (f : X ⟶ Y)
    (F : Sheaf J AddCommGrpCat.{v})
    (a : (freeRepresentableSheafFunctor J).obj Y ⟶ F) :
    freeSectionsEquiv J X F ((freeRepresentableSheafFunctor J).map f ≫ a) =
      F.obj.map f.op (freeSectionsEquiv J Y F a) := by
  change yonedaEquiv
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) F.obj)
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F)
        ((presheafToSheaf J AddCommGrpCat.{v}).map
          ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free |>.map (yoneda.map f)) ≫ a))) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

private def freeSectionsFunctorIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] :
    restrictedHomPresheafFunctor (freeRepresentableSheafFunctor J) ≅
      sheafToPresheaf J AddCommGrpCat.{v} ⋙
        (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u, v} :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun X ↦ ((freeSectionsEquiv J X.unop F).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro X Y f
      ext a
      exact congrArg ULift.up (freeSectionsEquiv_precomp J f.unop F a))) (by
        intro F G f
        ext X a
        exact congrArg ULift.up (freeSectionsEquiv_postcomp J X.unop f a))

/-- Homotopy classes from free representables compute objectwise homology of any
nonnegative complex of abelian sheaves; injectivity and Ext are not involved.
Source: Stacks Project, Section 01FT and Tag 03F3 (Hom-sections identification);
Derived Categories, Tag 06XR (homotopy classes from a single object).
(blueprint: lem-weil-pbc-free-representable-homotopy-homology)

Proof: Sheafification adjunction, the free abelian adjunction, and Yoneda identify
maps from the free abelian sheaf on U to G with G(U), additively and naturally in
both U and G. Apply this in every degree of the extension of K by zero. The Hom
complex from the degree-zero free sheaf becomes the lifted section complex.
Homotopy classes of maps to the q-shift are cocycles modulo coboundaries, hence
homology of that Hom complex. Evaluation of presheaves and additive universe lift
are exact and preserve homology. Extension by zero preserves homology at every
nonnegative degree; at q = 0 the incoming differential is zero on both sides.
Naturality in U of the adjunctions, extension comparison, and homology comparison
makes these isomorphisms commute with every restriction. Assemble them into a
natural isomorphism. This also applies to the empty site and the zero complex. -/
theorem freeRepresentableHomotopyPresheaf_homology
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (q : ℕ) :
    Nonempty
      (freeRepresentableHomotopyPresheaf J K q ⋙ AddCommGrpCat.uliftFunctor.{w, max u v} ≅
        (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (.up ℕ)).obj
          K).homology q ⋙ AddCommGrpCat.uliftFunctor.{max u w, v}) := by
  let A := freeRepresentableSheafFunctor J
  let E := sheafToPresheaf J AddCommGrpCat.{v}
  let U := (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.uliftFunctor.{u, v}
  let W := AddCommGrpCat.uliftFunctor.{w, max u v}
  let P := (E.mapHomologicalComplex (.up ℕ)).obj K
  obtain ⟨h⟩ := singleHomotopyPresheaf_homology A
    (K.extend ComplexShape.embeddingUpNat) (q : ℤ)
  let e := CochainComplex.mapExtendHomologyIso (E ⋙ U) K q
  let d : ((U.mapHomologicalComplex (.up ℕ)).obj P).homology q ≅ U.obj (P.homology q) :=
    (P.sc q).mapHomologyIso U
  let t : (P.homology q ⋙ AddCommGrpCat.uliftFunctor.{u, v}) ⋙ W ≅
      P.homology q ⋙ AddCommGrpCat.uliftFunctor.{max u w, v} :=
    NatIso.ofComponents (fun X ↦
      (show ULift.{w} (ULift.{u} ((P.homology q).obj X)) ≃+
        ULift.{max u w} ((P.homology q).obj X) from
          (AddEquiv.ulift.trans AddEquiv.ulift).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by intro X Y f; ext a; rfl)
  let c := (NatIso.mapHomologicalComplex (freeSectionsFunctorIso J) (.up ℤ)).app
    (K.extend ComplexShape.embeddingUpNat)
  let hc := (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (.up ℤ) (q : ℤ)).mapIso c
  let compIso := (Functor.mapHomologicalComplexCompIso (F := E) (G := U)
    (Iso.refl (E ⋙ U)) (.up ℕ)).app K
  let hc' := (HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (.up ℕ) q).mapIso compIso.symm
  let hd := h ≪≫ hc ≪≫ e ≪≫ hc' ≪≫ d
  exact ⟨Functor.isoWhiskerRight hd W ≪≫ t⟩
