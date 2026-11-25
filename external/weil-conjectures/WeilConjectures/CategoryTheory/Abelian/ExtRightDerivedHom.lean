/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Ext and the right-derived additive Hom functor

Source: Stacks Project, Derived Categories, Tag 06XR, Lemma 13.27.2.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Abelian CochainComplex HomComplex Limits Opposite

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  [HasInjectiveResolutions A]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extRightDerivedHomComplexIso (X : A) (K : CochainComplex A ℤ) :
    HomComplex ((CochainComplex.singleFunctor A 0).obj X) K ≅
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex
         (.up ℤ)).obj K) :=
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
private noncomputable def complexPostcomp (X : A) {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    HomComplex ((CochainComplex.singleFunctor A 0).obj X) K ⟶
      HomComplex ((CochainComplex.singleFunctor A 0).obj X) L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ a.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' := by simp }
  comm' i j hij := by
    ext a
    change δ i j (a.comp (Cochain.ofHom f) (add_zero i)) =
      (δ i j a).comp (Cochain.ofHom f) (add_zero j)
    rw [δ_comp_zero_cochain _ _ j (by simpa using hij)]
    simp

omit [HasExt A] [HasInjectiveResolutions A] in
set_option backward.isDefEq.respectTransparency false in
private lemma complexPostcomp_iso (X : A) {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    complexPostcomp X f ≫ (extRightDerivedHomComplexIso X L).hom =
      (extRightDerivedHomComplexIso X K).hom ≫
        ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).map f := by
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change Cochain.fromSingleEquiv (zero_add n)
    ((Cochain.fromSingleMk a (zero_add n)).comp (Cochain.ofHom f) (add_zero n)) = _
  rw [← Cochain.fromSingleMk_postcomp, Cochain.fromSingleEquiv_fromSingleMk]
  change _ = Cochain.fromSingleEquiv (zero_add n)
    (Cochain.fromSingleMk a (zero_add n)) ≫ f.f n
  rw [Cochain.fromSingleEquiv_fromSingleMk]

omit [HasInjectiveResolutions A] in
set_option backward.isDefEq.respectTransparency false in
private lemma extEquiv_postcomp (X : A) {Y Z : A} {f : Y ⟶ Z}
    (R : InjectiveResolution Y) (S : InjectiveResolution Z) (φ : R.Hom S f)
    (q : ℕ) (a : Cocycle ((CochainComplex.singleFunctor A 0).obj X) R.cochainComplex q) :
    (R.extEquivCohomologyClass.symm (CohomologyClass.mk a)).comp
        (Ext.mk₀ f) (add_zero q) =
      S.extEquivCohomologyClass.symm (CohomologyClass.mk (a.postcomp φ.hom')) := by
  obtain ⟨b, hb, rfl⟩ := Cocycle.fromSingleMk_surjective a q (zero_add _) (q + 1) rfl
  let c := b ≫ (R.cochainComplexXIso q q rfl).hom
  have hc : c ≫ R.cocomplex.d q (q + 1) = 0 := by
    dsimp [c]
    simpa only [← cancel_mono (R.cochainComplexXIso (q + 1) (q + 1) rfl).inv,
      Category.assoc, Limits.zero_comp, R.cochainComplex_d q (q + 1) q (q + 1) rfl rfl] using hb
  have ha : R.extEquivCohomologyClass.symm
      (CohomologyClass.mk (Cocycle.fromSingleMk b (zero_add (q : ℤ))
        (q + 1) rfl hb)) = R.extMk c (q + 1) rfl hc := by
    simp [InjectiveResolution.extMk, c]
  rw [ha, InjectiveResolution.extMk_comp_mk₀ c (q + 1) rfl hc φ]
  simp only [InjectiveResolution.extMk]
  congr 2
  rw [← Cocycle.fromSingleMk_postcomp]
  congr 1
  dsimp [c]
  simp [φ.hom'_f q q rfl]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extHomologyMapData (X : A) {Y Z : A} {f : Y ⟶ Z}
    (R : InjectiveResolution Y) (S : InjectiveResolution Z) (φ : R.Hom S f) (q : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ (q : ℤ)).map (complexPostcomp X φ.hom'))
      (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
        R.cochainComplex q)
      (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
        S.cochainComplex q) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun a ↦ a.postcomp φ.hom'
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  φH := R.extAddEquivCohomologyClass.symm.toAddCommGrpIso.hom ≫
    ((extFunctor q).obj (op X)).map f ≫ S.extAddEquivCohomologyClass.toAddCommGrpIso.hom
  commi := by
    ext a
    rfl
  commf' := by
    rw [← cancel_mono (HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor A 0).obj X) S.cochainComplex q).i]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    have hi : AddCommGrpCat.ofHom
        { toFun := fun a ↦ a.postcomp φ.hom'
          map_zero' := by ext; simp
          map_add' := by intros; ext; simp } ≫
        (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
          S.cochainComplex q).i =
        (HomComplex.leftHomologyData ((CochainComplex.singleFunctor A 0).obj X)
          R.cochainComplex q).i ≫ (complexPostcomp X φ.hom').f q := by
      ext a
      rfl
    rw [hi, ShortComplex.LeftHomologyData.f'_i_assoc]
    exact ((HomologicalComplex.shortComplexFunctor _ _ (q : ℤ)).map
      (complexPostcomp X φ.hom')).comm₁₂.symm
  commπ := by
    ext a
    change S.extEquivCohomologyClass
      ((R.extEquivCohomologyClass.symm (CohomologyClass.mk a)).comp
        (Ext.mk₀ f) (add_zero q)) = CohomologyClass.mk (a.postcomp φ.hom')
    rw [extEquiv_postcomp X R S φ q a, Equiv.apply_symm_apply]

/-- The objectwise comparison between Ext and derived Hom, constructed using the chosen
injective resolution and an isomorphism of Hom complexes. No existence witness is chosen.
Source: Stacks Project, Tag 06XR, Lemma 13.27.2 (injective-resolution computation). -/
private noncomputable def extRightDerivedHomObjIso (X Y : A) (q : ℕ) :
    ((extFunctor q).obj (op X)).obj Y ≅
      ((preadditiveCoyoneda.obj (op X)).rightDerived q).obj Y := by
  let R := injectiveResolution Y
  let E := preadditiveCoyoneda.obj (op X)
  exact R.extAddEquivCohomologyClass.toAddCommGrpIso ≪≫
    (HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor A 0).obj X) R.cochainComplex (q : ℤ)).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso
      (extRightDerivedHomComplexIso X R.cochainComplex) ≪≫
    (R.isoRightDerivedObjCochainComplex E q).symm

set_option backward.isDefEq.respectTransparency false in
private lemma extRightDerivedHomObjIso_naturality (X : A) {Y Z : A} (f : Y ⟶ Z) (q : ℕ) :
    ((extFunctor q).obj (op X)).map f ≫ (extRightDerivedHomObjIso X Z q).hom =
      (extRightDerivedHomObjIso X Y q).hom ≫
        ((preadditiveCoyoneda.obj (op X)).rightDerived q).map f := by
  let R := injectiveResolution Y
  let S := injectiveResolution Z
  let E := preadditiveCoyoneda.obj (op X)
  let φ : R.Hom S f :=
    ⟨InjectiveResolution.desc f S R, by simp [InjectiveResolution.desc_commutes_zero]⟩
  have h₁ := (extHomologyMapData X R S φ q).homologyMap_eq
  have h₂ := (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).congr_map
    (complexPostcomp_iso X φ.hom')
  have h₃ := R.isoRightDerivedObjCochainComplex_inv_naturality φ E q
  let cR : AddCommGrpCat.of (Ext X Y q) ≅ AddCommGrpCat.of
      (CohomologyClass ((singleFunctor A 0).obj X) R.cochainComplex q) :=
    (R.extAddEquivCohomologyClass (X := X) (n := q)).toAddCommGrpIso
  let cS : AddCommGrpCat.of (Ext X Z q) ≅ AddCommGrpCat.of
      (CohomologyClass ((singleFunctor A 0).obj X) S.cochainComplex q) :=
    (S.extAddEquivCohomologyClass (X := X) (n := q)).toAddCommGrpIso
  let hR := (HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor A 0).obj X) R.cochainComplex q).homologyIso
  let hS := (HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor A 0).obj X) S.cochainComplex q).homologyIso
  let kR := (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso
    (extRightDerivedHomComplexIso X R.cochainComplex)
  let kS := (HomologicalComplex.homologyFunctor _ _ (q : ℤ)).mapIso
    (extRightDerivedHomComplexIso X S.cochainComplex)
  change ((extFunctor q).obj (op X)).map f ≫
    ((cS ≪≫ hS.symm ≪≫ kS ≪≫ (S.isoRightDerivedObjCochainComplex E q).symm).hom) =
    ((cR ≪≫ hR.symm ≪≫ kR ≪≫ (R.isoRightDerivedObjCochainComplex E q).symm).hom) ≫
      (E.rightDerived q).map f
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change HomologicalComplex.homologyMap (complexPostcomp X φ.hom') q =
    hR.hom ≫ (cR.inv ≫ ((extFunctor q).obj (op X)).map f ≫ cS.hom) ≫ hS.inv at h₁
  have h₁' : cR.hom ≫ hR.inv ≫
      HomologicalComplex.homologyMap (complexPostcomp X φ.hom') q =
      ((extFunctor q).obj (op X)).map f ≫ cS.hom ≫ hS.inv := by
    rw [h₁]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h₁']
  simp only [Functor.map_comp] at h₂
  change HomologicalComplex.homologyMap (complexPostcomp X φ.hom') q ≫
      HomologicalComplex.homologyMap (extRightDerivedHomComplexIso X S.cochainComplex).hom q =
    HomologicalComplex.homologyMap (extRightDerivedHomComplexIso X R.cochainComplex).hom q ≫
      HomologicalComplex.homologyMap ((E.mapHomologicalComplex (.up ℤ)).map φ.hom') q at h₂
  erw [reassoc_of% h₂, h₃]
  rfl

/-- Ext in the second variable is the right-derived additive Hom functor.
Source: Stacks Project, Tag 06XR, Lemma 13.27.2 (injective-resolution computation).
(blueprint: lem-sc-ext-right-derived-hom)

Proof: Choose the standard injective resolution of each object. Mathlib identifies Ext
with cohomology classes in its Hom complex. The from-single additive equivalence gives
an isomorphism from that Hom complex to the complex obtained by applying additive Hom.
Taking homology and the right-derived computation gives the component isomorphisms.
For a morphism, lift it to a comparison map of injective resolutions. The Ext computation,
the Hom-complex isomorphism, and the derived computation all commute with that map,
so the component isomorphisms form a natural isomorphism. -/
theorem nonempty_extFunctor_iso_rightDerivedHom (X : A) (q : ℕ) :
    Nonempty ((extFunctor q).obj (op X) ≅
      (preadditiveCoyoneda.obj (op X)).rightDerived q) := by
  exact ⟨NatIso.ofComponents (fun Y ↦ extRightDerivedHomObjIso X Y q)
    (fun f ↦ extRightDerivedHomObjIso_naturality X f q)⟩

end CategoryTheory

