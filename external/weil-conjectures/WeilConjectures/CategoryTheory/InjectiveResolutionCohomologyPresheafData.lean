/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
public import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

@[expose] public section
universe u v w

namespace CategoryTheory.InjectiveResolution

open Opposite Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]
  {F : A} (I : InjectiveResolution F)

/-- The complex of additive Hom groups into the resolution, with precomposition maps. -/
private noncomputable def homComplexFunctor : Aᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ where
  obj X := ((preadditiveCoyoneda.obj X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex
  map f := (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map f)
    (ComplexShape.up ℕ)).app I.cocomplex
  map_id X := by
    simp only [Functor.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp f g := by
    simp only [Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- Homology of the additive Hom complex, contravariantly in its first argument. -/
private noncomputable def homologyFunctor (q : ℕ) : Aᵒᵖ ⥤ AddCommGrpCat.{v} :=
  I.homComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q

open CochainComplex HomComplex

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homComplexIso (X : A) (K : CochainComplex A ℤ) :
    HomComplex ((CochainComplex.singleFunctor A 0).obj X) K ≅
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.fromSingleEquiv (zero_add n)).toAddCommGrpIso) (by
      intro i j hij
      ext a
      obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
      change (Cochain.fromSingleEquiv (zero_add i)
        (Cochain.fromSingleMk a (zero_add i)) ≫ K.d i j) =
        (Cochain.fromSingleEquiv (zero_add j)
          (δ i j (Cochain.fromSingleMk a (zero_add i))))
      simp only [Cochain.δ_fromSingleMk, zero_add, Cochain.fromSingleEquiv_fromSingleMk])

set_option backward.isDefEq.respectTransparency false in
private noncomputable def complexPrecomp {X Y : A} (g : X ⟶ Y)
    (K : CochainComplex A ℤ) :
    HomComplex ((CochainComplex.singleFunctor A 0).obj Y) K ⟶
      HomComplex ((CochainComplex.singleFunctor A 0).obj X) K where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map g)).comp
        a (zero_add n)
      map_zero' := by simp
      map_add' := by simp }
  comm' i j hij := by
    ext a
    change δ i j ((Cochain.ofHom ((CochainComplex.singleFunctor A 0).map g)).comp
      a (zero_add i)) =
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map g)).comp
        (δ i j a) (zero_add j)
    exact δ_ofHom_comp _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma complexPrecomp_iso {X Y : A} (g : X ⟶ Y) (K : CochainComplex A ℤ) :
    complexPrecomp g K ≫ (homComplexIso X K).hom =
      (homComplexIso Y K).hom ≫
        (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map g.op) (.up ℤ)).app K := by
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change Cochain.fromSingleEquiv (zero_add n)
    ((Cochain.ofHom ((CochainComplex.singleFunctor A 0).map g)).comp
      (Cochain.fromSingleMk a (zero_add n)) (zero_add n)) = _
  rw [← Cochain.fromSingleMk_precomp, Cochain.fromSingleEquiv_fromSingleMk]
  change _ = g ≫ Cochain.fromSingleEquiv (zero_add n)
    (Cochain.fromSingleMk a (zero_add n))
  rw [Cochain.fromSingleEquiv_fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
private lemma extEquiv_precomp [HasExt.{w} A] {X Y : A} (g : X ⟶ Y) (q : ℕ)
    (a : Cocycle ((CochainComplex.singleFunctor A 0).obj Y) I.cochainComplex q) :
    (Ext.mk₀ g).comp (I.extEquivCohomologyClass.symm (CohomologyClass.mk a))
        (zero_add q) =
      I.extEquivCohomologyClass.symm
        (CohomologyClass.mk (a.precomp ((CochainComplex.singleFunctor A 0).map g))) := by
  obtain ⟨b, hb, rfl⟩ := Cocycle.fromSingleMk_surjective a q (zero_add _) (q + 1) rfl
  let c := b ≫ (I.cochainComplexXIso q q rfl).hom
  have hc : c ≫ I.cocomplex.d q (q + 1) = 0 := by
    dsimp [c]
    simpa only [← cancel_mono (I.cochainComplexXIso (q + 1) (q + 1) rfl).inv,
      Category.assoc, Limits.zero_comp, I.cochainComplex_d q (q + 1) q (q + 1) rfl rfl]
      using hb
  have ha : I.extEquivCohomologyClass.symm
      (CohomologyClass.mk (Cocycle.fromSingleMk b (zero_add (q : ℤ))
        (q + 1) rfl hb)) = I.extMk c (q + 1) rfl hc := by
    simp [InjectiveResolution.extMk, c]
  rw [ha, InjectiveResolution.mk₀_comp_extMk]
  simp only [InjectiveResolution.extMk]
  congr 2
  rw [← Cocycle.fromSingleMk_precomp]
  congr 1
  simp [c]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def precompHomologyMapData [HasExt.{w} A]
    {X Y : A} (g : X ⟶ Y) (q : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ (q : ℤ)).map
        (complexPrecomp g I.cochainComplex))
      (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj Y)
        I.cochainComplex q)
      (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
        I.cochainComplex q) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun a ↦ a.precomp ((CochainComplex.singleFunctor A 0).map g)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  φH := AddCommGrpCat.ofHom
    ((I.extAddEquivCohomologyClass (X := X) (n := q)).toAddMonoidHom.comp
      (((Ext.mk₀ g).precomp F (zero_add q)).comp
        (I.extAddEquivCohomologyClass (X := Y) (n := q)).symm.toAddMonoidHom))
  commi := by ext a; rfl
  commf' := by
    rw [← cancel_mono (HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex q).i]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    have hi : AddCommGrpCat.ofHom
        { toFun := fun a ↦ a.precomp ((CochainComplex.singleFunctor A 0).map g)
          map_zero' := by ext; simp
          map_add' := by intros; ext; simp } ≫
        (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
          I.cochainComplex q).i =
        (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj Y)
          I.cochainComplex q).i ≫ (complexPrecomp g I.cochainComplex).f q := by
      ext a
      rfl
    rw [hi, ShortComplex.LeftHomologyData.f'_i_assoc]
    exact ((HomologicalComplex.shortComplexFunctor _ _ (q : ℤ)).map
      (complexPrecomp g I.cochainComplex)).comm₁₂.symm
  commπ := by
    ext a
    change I.extEquivCohomologyClass
      ((Ext.mk₀ g).comp (I.extEquivCohomologyClass.symm (CohomologyClass.mk a))
        (zero_add q)) = _
    rw [extEquiv_precomp I g q a, Equiv.apply_symm_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
private lemma mapExtendIso_precomp {X Y : A} (g : X ⟶ Y) :
    (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map g.op) (.up ℤ)).app
        I.cochainComplex ≫
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
        (preadditiveCoyoneda.obj (op X))).hom =
    (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
      (preadditiveCoyoneda.obj (op Y))).hom ≫
      HomologicalComplex.extendMap (I.homComplexFunctor.map g.op)
        ComplexShape.embeddingUpNat := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : ∃ n : ℕ, (n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    dsimp only [InjectiveResolution.cochainComplex, HomologicalComplex.mapExtendIso,
      HomologicalComplex.Hom.isoOfComponents, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex]
    erw [HomologicalComplex.mapExtendX_hom_eq I.cocomplex
      (preadditiveCoyoneda.obj (op X)) (ComplexShape.embeddingUpNat.r_f n),
      HomologicalComplex.mapExtendX_hom_eq I.cocomplex
        (preadditiveCoyoneda.obj (op Y)) (ComplexShape.embeddingUpNat.r_f n),
      HomologicalComplex.extendMap_f _ _ (i := n) rfl]
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      homComplexFunctor, NatTrans.mapHomologicalComplex, eqToIso,
      ← Category.assoc, eqToHom_trans]
    have h := eqToHom_naturality
      (fun Z : A ↦ (preadditiveCoyoneda.map g.op).app Z)
      (congrArg (HomologicalComplex.extend.X I.cocomplex)
        (ComplexShape.embeddingUpNat.r_f n))
    let eX := (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).extendXIso ComplexShape.embeddingUpNat (i := n) rfl
    simpa only [eX, HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      eqToIso, Category.assoc, eqToHom_trans] using!
      congrArg (fun k ↦ k ≫ eX.inv) h
  · apply Limits.IsZero.eq_of_tgt
    apply HomologicalComplex.isZero_extend_X
    simpa using hi

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homologyToIntIso (X : A) (q : ℕ) :
    (I.homologyFunctor q).obj (op X) ≅
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex).homology (q : ℤ) := by
  let E := preadditiveCoyoneda.obj (op X)
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  exact (K.extendHomologyIso ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
      (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat E).symm

set_option backward.isDefEq.respectTransparency false in
private lemma homologyToIntIso_naturality {X Y : A} (g : X ⟶ Y) (q : ℕ) :
    (I.homologyFunctor q).map g.op ≫ (homologyToIntIso I X q).hom =
      (homologyToIntIso I Y q).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map g.op) (.up ℤ)).app
          I.cochainComplex) (q : ℤ) := by
  let eX := ((I.homComplexFunctor.obj (op X)).extendHomologyIso
    ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl)
  let eY := ((I.homComplexFunctor.obj (op Y)).extendHomologyIso
    ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl)
  let mX := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (preadditiveCoyoneda.obj (op X)))
  let mY := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (preadditiveCoyoneda.obj (op Y)))
  have h₁ := HomologicalComplex.extendHomologyIso_hom_naturality
    (I.homComplexFunctor.map g.op) ComplexShape.embeddingUpNat (j := q) rfl
  have h₂ := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).congr_map
    (mapExtendIso_precomp I g)
  simp only [Functor.map_comp] at h₂
  change HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (I.homComplexFunctor.map g.op)
        ComplexShape.embeddingUpNat) (q : ℤ) ≫ eX.hom =
    eY.hom ≫ (I.homologyFunctor q).map g.op at h₁
  change HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map g.op) (.up ℤ)).app
        I.cochainComplex) (q : ℤ) ≫ mX.hom =
    mY.hom ≫ HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap (I.homComplexFunctor.map g.op)
        ComplexShape.embeddingUpNat) (q : ℤ) at h₂
  change (I.homologyFunctor q).map g.op ≫ (eX.inv ≫ mX.inv) =
    (eY.inv ≫ mY.inv) ≫ _
  apply (cancel_epi eY.hom).1
  apply (cancel_mono mX.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h₁]
  erw [eX.hom_inv_id, Category.comp_id]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using!
    congrArg (fun k ↦ mY.inv ≫ k) h₂.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homologyObjIso (X : A) (q : ℕ) :
    (I.homologyFunctor q).obj (op X) ≅ AddCommGrpCat.of
      (CohomologyClass ((CochainComplex.singleFunctor A 0).obj X) I.cochainComplex q) :=
  homologyToIntIso I X q ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
      (homComplexIso X I.cochainComplex).symm ≪≫
    (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
      I.cochainComplex q).homologyIso

set_option backward.isDefEq.respectTransparency false in
private lemma homologyObjIso_naturality [HasExt.{w} A] {X Y : A} (g : X ⟶ Y) (q : ℕ) :
    (I.homologyFunctor q).map g.op ≫ (homologyObjIso I X q).hom =
      (homologyObjIso I Y q).hom ≫ (precompHomologyMapData I g q).φH := by
  have h₁ := homologyToIntIso_naturality I g q
  have h₂ := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).congr_map
    (complexPrecomp_iso g I.cochainComplex)
  simp only [Functor.map_comp] at h₂
  have h₃ := (precompHomologyMapData I g q).homologyMap_eq
  let aX := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    (homComplexIso X I.cochainComplex)
  let aY := (HomologicalComplex.homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso
    (homComplexIso Y I.cochainComplex)
  let bX := (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
    I.cochainComplex q).homologyIso
  let bY := (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj Y)
    I.cochainComplex q).homologyIso
  change HomologicalComplex.homologyMap (complexPrecomp g I.cochainComplex) (q : ℤ) ≫
    aX.hom = aY.hom ≫ HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map g.op) (.up ℤ)).app
        I.cochainComplex) (q : ℤ) at h₂
  change (I.homologyFunctor q).map g.op ≫
    ((homologyToIntIso I X q).hom ≫ aX.inv ≫ bX.hom) =
    ((homologyToIntIso I Y q).hom ≫ aY.inv ≫ bY.hom) ≫ _
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  apply congrArg ((homologyToIntIso I Y q).hom ≫ ·)
  apply (cancel_epi aY.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  erw [← reassoc_of% h₂]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change HomologicalComplex.homologyMap (complexPrecomp g I.cochainComplex) q ≫
    bX.hom = bY.hom ≫ (precompHomologyMapData I g q).φH
  change HomologicalComplex.homologyMap (complexPrecomp g I.cochainComplex) (q : ℤ) =
    bY.hom ≫ (precompHomologyMapData I g q).φH ≫ bX.inv at h₃
  rw [h₃]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homologyObjEquiv [HasExt.{w} A] (X : A) (q : ℕ) :
    (I.homologyFunctor q).obj (op X) ≃+ Ext.{w} X F q :=
  (homologyObjIso I X q).addCommGroupIsoToAddEquiv.trans
    I.extAddEquivCohomologyClass.symm

set_option backward.isDefEq.respectTransparency false in
/-- Ext is computed by the Hom complex of any injective resolution, naturally in the
first variable. Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 2.

Proof: Extend the resolution from natural to integer degrees by zero. The from-single
additive equivalence identifies the Hom complex from thedegree-zero single complex
with the degreewise additive Hom complex. Mathlib identifies its homology with
cohomology classes, and its Ext equivalence identifies those classes with Ext.
Extension by zero does not change homology in nonnegative degrees, including zero.
Precomposition acts on the single complex and on each Hom group. All the comparison
maps commute with it: on a cocycle this is associativity of composition, and on Ext
it is the formula for composing an Ext class represented by a cocycle with a
degree-zero morphism. Descending to cohomology gives the claimed natural isomorphism. -/
private theorem nonempty_homologyFunctor_iso_ext [HasExt.{w} A] (q : ℕ) :
    Nonempty (I.homologyFunctor q ⋙ AddCommGrpCat.uliftFunctor.{w} ≅
      (extFunctor.{w} q).flip.obj F ⋙ AddCommGrpCat.uliftFunctor.{v}) := by
  refine ⟨NatIso.ofComponents (fun X ↦
    ((AddEquiv.ulift.trans (homologyObjEquiv I X.unop q)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) ?_⟩
  intro X Y f
  ext a
  apply ULift.ext
  change homologyObjEquiv I Y.unop q
      ((I.homologyFunctor q).map f a.down) =
    (Ext.mk₀ f.unop).comp (homologyObjEquiv I X.unop q a.down) (zero_add q)
  have h := ConcreteCategory.congr_hom (homologyObjIso_naturality I f.unop q) a.down
  change (homologyObjIso I Y.unop q).hom ((I.homologyFunctor q).map f a.down) =
    (precompHomologyMapData I f.unop q).φH ((homologyObjIso I X.unop q).hom a.down) at h
  change I.extEquivCohomologyClass.symm
      ((homologyObjIso I Y.unop q).hom ((I.homologyFunctor q).map f a.down)) = _
  rw [h]
  change I.extEquivCohomologyClass.symm
    (I.extEquivCohomologyClass ((Ext.mk₀ f.unop).comp
      (I.extEquivCohomologyClass.symm ((homologyObjIso I X.unop q).hom a.down))
        (zero_add q))) = _
  exact Equiv.symm_apply_apply _ _

end CategoryTheory.InjectiveResolution

namespace CategoryTheory

open Opposite Abelian

private noncomputable abbrev freeSheafFunctor
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat.{v}

private noncomputable def freeSectionsEquiv
    {C : Type u} [Category.{v} C] (X : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda.obj X ⋙ AddCommGrpCat.free ⟶ P) ≃+ P.obj (op X) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (op X) (𝟙 X) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

private noncomputable def sectionsEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeSheafFunctor J).obj X ⟶ F) ≃+ F.obj.obj (op X) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ F).trans
    (freeSectionsEquiv X F.obj)

set_option backward.isDefEq.respectTransparency false in
private lemma sectionsEquiv_postcomp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C)
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (a : (freeSheafFunctor J).obj X ⟶ F) :
    sectionsEquiv J X G (a ≫ f) = f.hom.app (op X) (sectionsEquiv J X F a) := by
  change freeSectionsEquiv X G.obj
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ (a ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma sectionsEquiv_precomp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] {X Y : C} (f : X ⟶ Y)
    (F : Sheaf J AddCommGrpCat.{v}) (a : (freeSheafFunctor J).obj Y ⟶ F) :
    sectionsEquiv J X F ((freeSheafFunctor J).map f ≫ a) =
      F.obj.map f.op (sectionsEquiv J Y F a) := by
  change freeSectionsEquiv X F.obj
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _
      ((presheafToSheaf J AddCommGrpCat.{v}).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map f)) ≫
          a)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map f) ≫
      ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _ a))) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ f).symm

private noncomputable def sectionsComplexIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) (X : Cᵒᵖ) :
    ((AddCommGrpCat.uliftFunctor.{v, max u v}.mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (((preadditiveCoyoneda.obj ((freeSheafFunctor J).op.obj X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K)) ≅
    ((AddCommGrpCat.uliftFunctor.{max u v, v}.mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).asFunctor.obj X)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((AddEquiv.ulift.trans (sectionsEquiv J X.unop (K.X n))).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) (by
      intro i j hij
      ext a
      apply ULift.ext
      exact sectionsEquiv_postcomp J X.unop (K.d i j) a.down)

set_option backward.isDefEq.respectTransparency false in
/-- Objectwise comparison isomorphisms for the cohomology of an injective resolution,
with the restriction compatibility needed to assemble them into a natural isomorphism.
Source: blueprint lem-sc-injective-resolution-cohomology-presheaf, Step 2.
(blueprint: lem-sc-injective-resolution-cohomology-presheaf-data) -/
theorem Sheaf.injectiveResolution_cohomologyPresheaf_data
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (q : ℕ) :
    ∃ e : ∀ X : Cᵒᵖ,
      ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).obj X ≅
      (F.cohomologyPresheaf q).obj X,
      ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
        ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).map f ≫
            (e Y).hom = (e X).hom ≫ (F.cohomologyPresheaf q).map f := by
  let R := freeSheafFunctor J
  let K := (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor
  let H := K ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q
  let L := AddCommGrpCat.uliftFunctor.{max u v, v}
  let M := AddCommGrpCat.uliftFunctor.{v, max u v}
  have c : (R.op ⋙ I.homComplexFunctor) ⋙ M.mapHomologicalComplex (ComplexShape.up ℕ) ≅
      K ⋙ L.mapHomologicalComplex (ComplexShape.up ℕ) :=
    NatIso.ofComponents (fun X ↦ sectionsComplexIso J I.cocomplex X) (by
      intro X Y f
      ext n a
      apply ULift.ext
      exact sectionsEquiv_precomp J f.unop (I.cocomplex.X n) a.down)
  have s : (R.op ⋙ I.homologyFunctor q) ⋙ M ≅ H ⋙ L := by
    have hM : (R.op ⋙ I.homComplexFunctor) ⋙ M.mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℕ) q ≅
        (R.op ⋙ I.homologyFunctor q) ⋙ M :=
      NatIso.ofComponents (fun X ↦
        ((I.homComplexFunctor.obj (R.op.obj X)).sc q).mapHomologyIso M) (by
          intro X Y f
          exact ShortComplex.mapHomologyIso_hom_naturality
            ((HomologicalComplex.shortComplexFunctor _ _ q).map
              (I.homComplexFunctor.map (R.op.map f))) M)
    have hL : K ⋙ L.mapHomologicalComplex (.up ℕ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℕ) q ≅ H ⋙ L :=
      NatIso.ofComponents (fun X ↦ ((K.obj X).sc q).mapHomologyIso L) (by
        intro X Y f
        exact ShortComplex.mapHomologyIso_hom_naturality
          ((HomologicalComplex.shortComplexFunctor _ _ q).map (K.map f)) L)
    exact hM.symm ≪≫ Functor.isoWhiskerRight c
      (HomologicalComplex.homologyFunctor _ (.up ℕ) q) ≪≫ hL
  obtain ⟨t⟩ := InjectiveResolution.nonempty_homologyFunctor_iso_ext.{_, _, v} I q
  have e : H ≅ F.cohomologyPresheaf q :=
    Functor.fullyFaithfulCancelRight L (s.symm ≪≫ Functor.isoWhiskerLeft R.op t)
  exact ⟨fun X ↦ e.app X, fun f ↦ e.hom.naturality f⟩

end CategoryTheory
