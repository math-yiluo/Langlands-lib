/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.Functor

/-! # Homotopy maps from single objects and homology of Hom presheaves -/

@[expose] public noncomputable section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

/-- The functor of additive Hom presheaves restricted along a family of objects. -/
def restrictedHomPresheafFunctor
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [Preadditive D] (A : C ⥤ D) : D ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v'} :=
  preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj A.op

instance restrictedHomPresheafFunctor_additive
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [Preadditive D] (A : C ⥤ D) : (restrictedHomPresheafFunctor A).Additive where
  map_add := by
    intro X Y f g
    ext U a
    change a ≫ (f + g) = a ≫ f + a ≫ g
    exact Preadditive.comp_add _ _ _ a f g

namespace SingleHomotopyAux

open CochainComplex HomComplex

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  {S S' : CochainComplex D ℤ} (L : CochainComplex D ℤ)

private def preMap (g : S' ⟶ S) : HomComplex S L ⟶ HomComplex S' L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ (Cochain.ofHom g).comp a (zero_add n)
      map_zero' := by simp
      map_add' := fun a b ↦ Cochain.comp_add _ _ _ _ }
  comm' i j _ := by
    ext a
    exact δ_ofHom_comp g a j

private def preCocycle (g : S' ⟶ S) (n : ℤ) :
    Cocycle S L n →+ Cocycle S' L n where
  toFun a := a.precomp g
  map_zero' := by apply Cocycle.ext; simp [Cocycle.precomp]
  map_add' a b := by apply Cocycle.ext; simp [Cocycle.precomp, Cochain.comp_add]

private def preClass (g : S' ⟶ S) (n : ℤ) :
    CohomologyClass S L n →+ CohomologyClass S' L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom S' L n).comp (preCocycle L g n)) (by
      rintro a ⟨m, hm, b, hb⟩
      change CohomologyClass.mk (a.precomp g) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, (Cochain.ofHom g).comp b (zero_add m), ?_⟩
      rw [δ_ofHom_comp, hb]
      rfl)

private def preHomologyData (g : S' ⟶ S) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (preMap L g))
      (leftHomologyData S L n) (leftHomologyData S' L n) where
  φK := AddCommGrpCat.ofHom (preCocycle L g n)
  φH := AddCommGrpCat.ofHom (preClass L g n)
  commi := by ext a; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData S' L n).i).1
    rw [Category.assoc]
    change _ ≫ ((leftHomologyData S L n).i ≫ (preMap L g).f n) = _
    rw [← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((preMap L g).comm _ _).symm
  commπ := by ext a; rfl

private lemma pre_homologyClass_naturality (g : S' ⟶ S) (n : ℤ) :
    HomologicalComplex.homologyMap (preMap L g) n ≫
        (leftHomologyData S' L n).homologyIso.hom =
      (leftHomologyData S L n).homologyIso.hom ≫
        AddCommGrpCat.ofHom (preClass L g n) := by
  have h := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (preMap L g))
    (leftHomologyData S L n) (leftHomologyData S' L n)
  rw [(preHomologyData L g n).leftHomologyMap'_eq] at h
  exact h.symm

private lemma pre_homAddEquiv (g : S' ⟶ S) (n : ℤ) (a : CohomologyClass S L n) :
    CohomologyClass.homAddEquiv (preClass L g n a) =
      (HomotopyCategory.quotient D (.up ℤ)).map g ≫
        CohomologyClass.homAddEquiv a := by
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective a
  change CohomologyClass.toHom (.mk (a.precomp g)) =
    (HomotopyCategory.quotient D (.up ℤ)).map g ≫ CohomologyClass.toHom (.mk a)
  rw [CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp,
    Functor.map_comp, CohomologyClass.toHom_mk]

variable {C : Type u} [Category.{v} C] (A : C ⥤ D)

private abbrev homPresheafComplex :=
  ((restrictedHomPresheafFunctor A).mapHomologicalComplex (.up ℤ)).obj L

private def singleComplexIso (U : Cᵒᵖ) :
    HomComplex ((CochainComplex.singleFunctor D 0).obj (A.obj U.unop)) L ≅
      (homPresheafComplex L A).asFunctor.obj U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.fromSingleEquiv (zero_add n)).toAddCommGrpIso) (by
      intro i j _
      ext a
      obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
      change Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk a (zero_add i)) ≫
          L.d i j = Cochain.fromSingleEquiv (zero_add j)
            (δ i j (Cochain.fromSingleMk a (zero_add i)))
      simp only [Cochain.δ_fromSingleMk, zero_add, Cochain.fromSingleEquiv_fromSingleMk])

private lemma singleComplexIso_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    preMap L ((CochainComplex.singleFunctor D 0).map (A.map f.unop)) ≫
        (singleComplexIso L A V).hom =
      (singleComplexIso L A U).hom ≫ (homPresheafComplex L A).asFunctor.map f := by
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change Cochain.fromSingleEquiv (zero_add n)
      ((Cochain.ofHom ((CochainComplex.singleFunctor D 0).map (A.map f.unop))).comp
        (Cochain.fromSingleMk a (zero_add n)) (zero_add n)) =
    A.map f.unop ≫ Cochain.fromSingleEquiv (zero_add n)
      (Cochain.fromSingleMk a (zero_add n))
  rw [← Cochain.fromSingleMk_precomp]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]

private def evaluationHomologyIso (P : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v'}) ℤ)
    (n : ℤ) :
    P.asFunctor ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{v'} (.up ℤ) n ≅
      P.homology n :=
  NatIso.ofComponents
    (fun U ↦ (P.sc n).mapHomologyIso ((evaluation _ _).obj U)) (by
      intro U V f
      have h := (P.sc n).homologyMap_mapNatTrans ((evaluation _ _).map f)
      change HomologicalComplex.homologyMap (P.asFunctor.map f) n = _ at h
      change HomologicalComplex.homologyMap (P.asFunctor.map f) n ≫ _ = _
      rw [h]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)

private def homotopyHomologyObjIso (U : Cᵒᵖ) (n : ℤ) :
    AddCommGrpCat.of
      ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((CochainComplex.singleFunctor D 0).obj (A.obj U.unop)) ⟶
        (HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧)) ≅
      ((homPresheafComplex L A).asFunctor.obj U).homology n :=
  CohomologyClass.homAddEquiv.symm.toAddCommGrpIso ≪≫
    (leftHomologyData _ L n).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ n).mapIso (singleComplexIso L A U)

private lemma homotopyHomologyObjIso_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    ((A ⋙ CochainComplex.singleFunctor D 0 ⋙ HomotopyCategory.quotient D (.up ℤ)).op ⋙
        preadditiveYoneda.obj ((HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧))).map f ≫
      (homotopyHomologyObjIso L A V n).hom =
    (homotopyHomologyObjIso L A U n).hom ≫
      HomologicalComplex.homologyMap ((homPresheafComplex L A).asFunctor.map f) n := by
  let S := (CochainComplex.singleFunctor D 0).obj (A.obj U.unop)
  let T := (CochainComplex.singleFunctor D 0).obj (A.obj V.unop)
  let g : T ⟶ S := (CochainComplex.singleFunctor D 0).map (A.map f.unop)
  let hS := (leftHomologyData S L n).homologyIso
  let hT := (leftHomologyData T L n).homologyIso
  let eS : AddCommGrpCat.of (CohomologyClass S L n) ≅
      AddCommGrpCat.of ((HomotopyCategory.quotient D (.up ℤ)).obj S ⟶
        (HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧)) :=
    CohomologyClass.homAddEquiv.toAddCommGrpIso
  let eT : AddCommGrpCat.of (CohomologyClass T L n) ≅
      AddCommGrpCat.of ((HomotopyCategory.quotient D (.up ℤ)).obj T ⟶
        (HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧)) :=
    CohomologyClass.homAddEquiv.toAddCommGrpIso
  have he : eS.hom ≫
      ((A ⋙ CochainComplex.singleFunctor D 0 ⋙ HomotopyCategory.quotient D (.up ℤ)).op ⋙
        preadditiveYoneda.obj ((HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧))).map f =
        AddCommGrpCat.ofHom (preClass L g n) ≫ eT.hom := by
    ext a
    exact (pre_homAddEquiv L g n a).symm
  have hh := pre_homologyClass_naturality L g n
  have hc := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v'} (.up ℤ) n).map)
    (singleComplexIso_naturality L A f)
  simp only [HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] at hc
  change _ ≫ (eT.inv ≫ hT.inv ≫
      HomologicalComplex.homologyMap (singleComplexIso L A V).hom n) =
    (eS.inv ≫ hS.inv ≫ HomologicalComplex.homologyMap (singleComplexIso L A U).hom n) ≫ _
  rw [← cancel_epi eS.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [reassoc_of% he, Iso.hom_inv_id_assoc]
  rw [← cancel_epi hS.hom]
  simp only [Iso.hom_inv_id_assoc]
  erw [← reassoc_of% hh, Iso.hom_inv_id_assoc]
  exact hc

end SingleHomotopyAux

/-- Homotopy maps out of degree-zero single objects are homology of the degreewise
Hom presheaf.
Source: Mathlib HomComplexCohomology.lean, `CohomologyClass.homAddEquiv` and
`leftHomologyData`; HomComplexSingle.lean, `Cochain.fromSingleEquiv`; and
ShortComplex/PreservesHomology.lean, `homologyMap_mapNatTrans`.
(blueprint: lem-weil-pbc-single-homotopy-presheaf-homology)

Proof: At U, cochains from A(U)[0] to L are precisely maps A(U) -> L^n.
The equivalence `Cochain.fromSingleEquiv` commutes with the differentials:
`delta_fromSingleMk` identifies the differential with postcomposition by d_L.
It therefore identifies the Hom complex with evaluation at U of the degreewise
Hom presheaf complex. Mathlib's `leftHomologyData` identifies its homology with
cohomology classes, and `CohomologyClass.homAddEquiv` identifies those classes with
maps from A(U)[0] to L[n] in the homotopy category. Evaluation preserves homology.
All these identifications commute with precomposition by A(f): on cochains this
is `fromSingleMk_precomp`, on cocycles it is precomposition, and on the quotient
it follows by surjectivity of the cocycle projection. Thus the component
isomorphisms commute with restriction maps and assemble into a natural isomorphism.
This works in all integer degrees and for an empty indexing category. -/
theorem singleHomotopyPresheaf_homology
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [Abelian D] (A : C ⥤ D) (L : CochainComplex D ℤ) (n : ℤ) :
    Nonempty
      ((A ⋙ CochainComplex.singleFunctor D 0 ⋙ HomotopyCategory.quotient D (.up ℤ)).op ⋙
          preadditiveYoneda.obj ((HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧)) ≅
        (((restrictedHomPresheafFunctor A).mapHomologicalComplex (.up ℤ)).obj L).homology
          n) := by
  let e :
      (A ⋙ CochainComplex.singleFunctor D 0 ⋙ HomotopyCategory.quotient D (.up ℤ)).op ⋙
          preadditiveYoneda.obj ((HomotopyCategory.quotient D (.up ℤ)).obj (L⟦n⟧)) ≅
        ((((restrictedHomPresheafFunctor A).mapHomologicalComplex (.up ℤ)).obj L).asFunctor ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v'} (.up ℤ) n) :=
    NatIso.ofComponents
      (fun U ↦ SingleHomotopyAux.homotopyHomologyObjIso L A U n)
      (fun f ↦ SingleHomotopyAux.homotopyHomologyObjIso_naturality L A f n)
  exact ⟨e ≪≫ SingleHomotopyAux.evaluationHomologyIso
    (((restrictedHomPresheafFunctor A).mapHomologicalComplex (.up ℤ)).obj L) n⟩
