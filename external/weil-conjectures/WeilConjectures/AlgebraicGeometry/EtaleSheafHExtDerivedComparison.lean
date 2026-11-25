/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Comparison of Ext sheaf cohomology with derived global sections

Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI;
Etale Cohomology, the cohomology convention used in Lemma 03Q5.
(blueprint: lem-weil-pbc-sheafH-ext-derived-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace EtaleComparisonAux

open CochainComplex HomComplex Limits

universe v w

variable {C : Type w} [Category.{v} C] [Preadditive C]
  {S K L : CochainComplex C ℤ}

private noncomputable def postMap (S : CochainComplex C ℤ) (f : K ⟶ L) :
    HomComplex S K ⟶ HomComplex S L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ a.comp (.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' := fun a b ↦ Cochain.add_comp _ _ _ _ }
  comm' i j hij := by
    ext a
    change δ i j (a.comp (.ofHom f) (add_zero i)) =
      (δ i j a).comp (.ofHom f) (add_zero j)
    exact δ_comp_ofHom a f j

private def postCocycle (f : K ⟶ L) (n : ℤ) :
    Cocycle S K n →+ Cocycle S L n where
  toFun a := a.postcomp f
  map_zero' := by apply Cocycle.ext; simp [Cocycle.postcomp]
  map_add' a b := by apply Cocycle.ext; simp [Cocycle.postcomp, Cochain.add_comp]

private def postClass (f : K ⟶ L) (n : ℤ) :
    CohomologyClass S K n →+ CohomologyClass S L n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom S L n).comp (postCocycle f n)) (by
      rintro a ⟨m, hm, b, hb⟩
      change CohomologyClass.mk (a.postcomp f) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, b.comp (.ofHom f) (add_zero m), ?_⟩
      rw [δ_comp_ofHom, hb]
      rfl)

private lemma postClass_mk (f : K ⟶ L) (n : ℤ) (a : Cocycle S K n) :
    postClass f n (.mk a) = .mk (a.postcomp f) := rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def postHomologyData (f : K ⟶ L) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (postMap S f))
      (leftHomologyData S K n) (leftHomologyData S L n) where
  φK := AddCommGrpCat.ofHom (postCocycle f n)
  φH := AddCommGrpCat.ofHom (postClass f n)
  commi := by ext a; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData S L n).i).1
    rw [Category.assoc]
    change _ ≫ ((leftHomologyData S K n).i ≫ (postMap S f).f n) = _
    rw [← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((postMap S f).comm _ _).symm
  commπ := by ext a; rfl

set_option backward.isDefEq.respectTransparency false in
private lemma homologyClass_naturality (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap (postMap S f) n ≫
        (leftHomologyData S L n).homologyIso.hom =
      (leftHomologyData S K n).homologyIso.hom ≫
        AddCommGrpCat.ofHom (postClass f n) := by
  have h := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (postMap S f))
    (leftHomologyData S K n) (leftHomologyData S L n)
  rw [(postHomologyData f n).leftHomologyMap'_eq] at h
  exact h.symm

end EtaleComparisonAux

namespace EtaleComparisonAux

open CochainComplex HomComplex Limits

universe v w

variable {C : Type w} [Category.{v} C] [Abelian C] [HasExt.{v} C]

set_option backward.isDefEq.respectTransparency false in
private lemma extClass_naturality {A B B' : C} (f : B ⟶ B')
    (R : InjectiveResolution B) (R' : InjectiveResolution B') (φ : R.Hom R' f)
    (n : ℕ) (a : Abelian.Ext A B n) :
    postClass φ.hom' n (R.extAddEquivCohomologyClass a) =
      R'.extAddEquivCohomologyClass (a.comp (Abelian.Ext.mk₀ f) (add_zero n)) := by
  obtain ⟨a, ha, rfl⟩ := R.extMk_surjective a (n + 1) rfl
  simp only [InjectiveResolution.extAddEquivCohomologyClass_apply,
    InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extMk_comp_mk₀ _ _ _ _ φ, postClass_mk]
  congr 1
  rw [← Cocycle.fromSingleMk_postcomp]
  congr 1
  simp [φ.hom'_f n n rfl]

end EtaleComparisonAux

namespace AlgebraicGeometry.Scheme

open CochainComplex HomComplex Limits Opposite

private noncomputable abbrev ZSheaf (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private noncomputable def sectionsEquiv (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (ZSheaf X ⟶ F) ≃+ (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F :=
  ((constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

private lemma sectionsEquiv_naturality (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (a : ZSheaf X ⟶ F) :
    sectionsEquiv X G (a ≫ f) =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map f (sectionsEquiv X F a) := by
  dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def complexSectionsIso (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj (ZSheaf X)) K ≅
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      (sectionsEquiv X (K.X n))).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        simpa [HomComplex, Cochain.δ_fromSingleMk,
          Cochain.fromSingleEquiv_fromSingleMk] using!
          (sectionsEquiv_naturality X (K.d i j) a).symm)

set_option backward.isDefEq.respectTransparency false in
private lemma complexSectionsIso_naturality (X : Scheme.{u})
    {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ}
    (f : K ⟶ L) :
    EtaleComparisonAux.postMap ((CochainComplex.singleFunctor _ 0).obj (ZSheaf X)) f ≫
        (complexSectionsIso X L).hom =
      (complexSectionsIso X K).hom ≫
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex _).map f := by
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change sectionsEquiv X (L.X n)
    ((Cochain.fromSingleEquiv (zero_add n))
      ((Cochain.fromSingleMk a (zero_add n)).comp (.ofHom f) (add_zero n))) =
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (f.f n)
      (sectionsEquiv X (K.X n)
        ((Cochain.fromSingleEquiv (zero_add n)) (Cochain.fromSingleMk a (zero_add n))))
  rw [← Cochain.fromSingleMk_postcomp]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact sectionsEquiv_naturality X (f.f n) a

private noncomputable def classSectionsIso (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (n : ℤ) :
    AddCommGrpCat.of
        (CohomologyClass ((CochainComplex.singleFunctor _ 0).obj (ZSheaf X)) K n) ≅
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
        K).homology n :=
  (leftHomologyData _ K n).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (complexSectionsIso X K)

set_option backward.isDefEq.respectTransparency false in
private lemma classSectionsIso_naturality (X : Scheme.{u})
    {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ}
    (f : K ⟶ L) (n : ℤ) :
    AddCommGrpCat.ofHom (EtaleComparisonAux.postClass f n) ≫
        (classSectionsIso X L n).hom =
      (classSectionsIso X K n).hom ≫ HomologicalComplex.homologyMap
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex _).map
          f) n := by
  have h := EtaleComparisonAux.homologyClass_naturality
    (S := (CochainComplex.singleFunctor _ 0).obj (ZSheaf X)) f n
  have h' := congrArg ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map)
    (complexSectionsIso_naturality X f)
  simp only [HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyMap_comp] at h'
  dsimp only [classSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← cancel_epi (leftHomologyData _ K n).homologyIso.hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% h, Iso.hom_inv_id_assoc]
  exact h'

private noncomputable def sheafHRightDerivedIso (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (Sheaf.functorH.{u + 1} X.smallEtaleTopology n).obj F ≅
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived n).obj F :=
  (injectiveResolution F).extAddEquivCohomologyClass.toAddCommGrpIso ≪≫
    classSectionsIso X (injectiveResolution F).cochainComplex n ≪≫
    ((injectiveResolution F).isoRightDerivedObjCochainComplex
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) n).symm

set_option backward.isDefEq.respectTransparency false in
private lemma sheafHRightDerivedIso_naturality (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G) (n : ℕ) :
    (Sheaf.functorH.{u + 1} X.smallEtaleTopology n).map f ≫
        (sheafHRightDerivedIso X G n).hom =
      (sheafHRightDerivedIso X F n).hom ≫
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived n).map f := by
  let φ : (injectiveResolution F).Hom (injectiveResolution G) f :=
    ⟨InjectiveResolution.desc f _ _, by simp [InjectiveResolution.desc_commutes_zero]⟩
  have he : (Sheaf.functorH.{u + 1} X.smallEtaleTopology n).map f ≫
      (injectiveResolution G).extAddEquivCohomologyClass.toAddCommGrpIso.hom =
    (injectiveResolution F).extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
      AddCommGrpCat.ofHom (EtaleComparisonAux.postClass φ.hom' (n : ℤ)) := by
    ext a
    exact (EtaleComparisonAux.extClass_naturality f _ _ φ n a).symm
  have hc := classSectionsIso_naturality X φ.hom' (n : ℤ)
  have hr := (injectiveResolution F).isoRightDerivedObjCochainComplex_inv_naturality
    φ (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) n
  dsimp only [sheafHRightDerivedIso, Iso.trans_hom, Iso.symm_hom]
  rw [reassoc_of% he, reassoc_of% hc, hr]
  simp only [Category.assoc]

/-- Ext cohomology of abelian etale sheaves agrees naturally with the homology of
 derived global sections. No compactness, dimension, or torsion assumption is needed.
 Source: Stacks Project, Derived Categories, Definition 015A and Lemma 05TI;
 Etale Cohomology, Lemma 03Q5, using the same injective-resolution definition of cohomology.
 (blueprint: lem-weil-pbc-sheafH-ext-derived-comparison).

 Proof: Choose an injective resolution of each sheaf F. A bounded-below injective
 resolution is K-injective, so applying global sections computes the right-hand functor,
 by lem-sp-derived-functor-single-identification. On the left, Sheaf.H is Ext from the
 constant integer sheaf. Compute this Ext group with the same injective resolution;
 maps from the constant integer sheaf to each injective term identify with global
 sections by the constant-sheaf/global-sections adjunction and evaluation at 1 in Z.
 These identifications commute with the differentials, hence induce additive
 isomorphisms on cohomology. For a sheaf morphism, lift it to the injective resolutions;
 both constructions use the same lift. Lifts are unique up to homotopy, so the
 isomorphisms are independent of choices and natural. Package them as a natural
 isomorphism. This also handles degree zero and the empty scheme. -/
theorem nonempty_sheafH_extDerivedIso (X : Scheme.{u}) (q : ℕ) :
    Nonempty (Sheaf.functorH.{u + 1} X.smallEtaleTopology q ≅
      DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let e : Sheaf.functorH.{u + 1} X.smallEtaleTopology q ≅ Γ.rightDerived q :=
    NatIso.ofComponents (fun F ↦ sheafHRightDerivedIso X F q)
      (fun f ↦ sheafHRightDerivedIso_naturality X f q)
  let e' : DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ) ≅ Γ.rightDerived q :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        Γ.rightDerivedFunctorPlusCompatibility.symm)
      (DerivedCategory.homologyFunctor AddCommGrpCat (q : ℤ)) ≪≫
        Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  exact ⟨e ≪≫ e'.symm⟩

end AlgebraicGeometry.Scheme
