/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Resolution-normalized module/Ext comparisons

The comparisons below are constructed from section complexes, not selected from
an existence assertion about natural equivalences.
Source: Stacks Project, Tags 03FD, 01FT and 06XR.
(blueprint: new-module-cohomology-ext-resolution-naturality)
-/

@[expose] public section
universe u u₁
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
namespace ExtEdgeResolution

open CategoryTheory.Abelian CochainComplex HomComplex
section
variable {A : Type u₁} [Category.{u} A] [Abelian A] [HasExt.{u} A]
  [HasInjectiveResolutions A]
set_option backward.isDefEq.respectTransparency false in
noncomputable def extRightDerivedHomComplexIso (X : A) (K : CochainComplex A ℤ) :
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
noncomputable def extRightDerivedHomObjIso (X Y : A) (q : ℕ) :
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
lemma extRightDerivedHomObjIso_naturality (X : A) {Y Z : A} (f : Y ⟶ Z) (q : ℕ) :
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

end

noncomputable def freeSectionsEquiv
    {C : Type u} [SmallCategory C] (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (op U) (𝟙 U) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

noncomputable def sectionsEquiv
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ F).trans
    (freeSectionsEquiv U F.obj)

lemma sectionsEquiv_naturality
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C)
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G)
    (a : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    sectionsEquiv J U G (a ≫ f) = f.hom.app (op U) (sectionsEquiv J U F a) := by
  dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeSectionsEquiv]
  rfl

noncomputable def sectionsIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) :
    preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
  NatIso.ofComponents (fun F ↦ (sectionsEquiv J U F).toAddCommGrpIso) (by
    intro F G f
    ext a
    exact sectionsEquiv_naturality J U f a)

def derivedSectionsIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) (q : ℕ) :
    (preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free)))).rightDerived q ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q := by
  let s := sectionsIso J U
  exact
    { hom := NatTrans.rightDerived s.hom q
      inv := NatTrans.rightDerived s.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, s.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, s.inv_hom_id,
        NatTrans.rightDerived_id] }

set_option backward.isDefEq.respectTransparency false in
def siteSectionsNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    (U : C) (q : ℕ) :
    Sheaf.cohomologyPresheafFunctor J q ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q := by
  let e : (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      (preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)))).rightDerived q :=
    NatIso.ofComponents (fun F ↦ extRightDerivedHomObjIso
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F q)
      (fun φ ↦ extRightDerivedHomObjIso_naturality
        ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) φ q)
  exact (show Sheaf.cohomologyPresheafFunctor J q ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free))) from Iso.refl _) ≪≫ e ≪≫
          derivedSectionsIso J U q

def siteSectionsObjIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) (q : ℕ) :
    Sheaf.H' F q U ≅
      ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj F :=
  (siteSectionsNatIso J U q).app F

/-- Identify evaluated sheaf cohomology with its fixed Ext functor before specialization.
Source: Stacks Project, Tag 06XR; this is the definition of sheaf cohomology.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def siteExtNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (q : ℕ) :
    Sheaf.cohomologyPresheafFunctor J q ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      (CategoryTheory.Abelian.extFunctor q).obj
        (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
          (yoneda.obj U ⋙ AddCommGrpCat.free))) :=
  Iso.refl _

/-- Use the native H functor after identifying its constant Ext source.
Source: Stacks Project, Tag 06XR; this is the definition of `Sheaf.functorH`.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def siteHNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (q : ℕ) :
    (CategoryTheory.Abelian.extFunctor q).obj
      (op ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ≅
        Sheaf.functorH J q :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency true in
/-- The original additive Ext source-change equivalence, packaged naturally in coefficients.
Source: Stacks Project, Tag 06XR; functoriality of Ext in its two arguments.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def extSourceNatIso
    {A : Type u₁} [Category.{u} A] [Abelian A] [HasExt.{u} A]
    {M N : A} (e : M ≅ N) (q : ℕ) :
    (Abelian.extFunctor q).obj (op M) ≅ (Abelian.extFunctor q).obj (op N) :=
  NatIso.ofComponents
    (F := (Abelian.extFunctor q).obj (op M))
    (G := (Abelian.extFunctor q).obj (op N))
    (fun (Z : A) ↦ (Abelian.Ext.precompAddEquiv e Z q).symm.toAddCommGrpIso)
    (by
      intro Z W f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      change (Abelian.Ext.mk₀ e.inv).comp
          (x.comp (Abelian.Ext.mk₀ f) (add_zero q)) (zero_add q) =
        ((Abelian.Ext.mk₀ e.inv).comp x (zero_add q)).comp
          (Abelian.Ext.mk₀ f) (add_zero q)
      exact (Abelian.Ext.comp_assoc_of_third_deg_zero
        (Abelian.Ext.mk₀ e.inv) x (Abelian.Ext.mk₀ f) (zero_add q)).symm)


def terminalSourceIso (X : Scheme.{u}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  let e : yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free ≅
      (Functor.const X.Opensᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : X.Opens)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro z
        simp [FreeAbelianGroup.uniqueEquiv])
  exact (presheafToSheaf _ AddCommGrpCat.{u}).mapIso e

theorem forgottenInjectiveAcyclic (X : Scheme.{u})
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [Injective I] :
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).rightAcyclic
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj I) := by
  intro n
  let : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj I)
      (n + 1) (⊤ : X.Opens)) :=
    injective_module_abelian_acyclic ⊤ I (n + 1) (Nat.succ_pos n)
  exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
    (siteSectionsObjIso _ ⊤ _ (n + 1)).symm

/-- Forgetting scalars in the standard derived-functor resolution comparison.
Source: Stacks Project, Tag 03FD; exact forgetting commutes with homology.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def resolutionForgetObjIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
    (G : A ⥤ B) (V : B ⥤ D) [G.Additive] [V.Additive] [V.PreservesHomology]
    {M : A} (I : InjectiveResolution M) (q : ℕ) :
    V.obj ((G.rightDerived q).obj M) ≅
      ((V.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homology q :=
  V.mapIso (I.isoRightDerivedObj G q) ≪≫
    ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc q).mapHomologyIso
      V).symm

/-- The two ways of forming abelian section homology agree degreewise.
This identification is checked before substituting an injective resolution.
Source: Stacks Project, Tag 03FD, common section complex.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def sectionHomologyIso (X : Scheme.{u}) (q : ℕ) :
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙
      (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q) ≅
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
        (ComplexShape.up ℕ) ⋙
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).mapHomologicalComplex
          (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) q) :=
  Iso.refl _

/-- Common-resolution comparison for exact forgetting of scalars.
Source: Stacks Project, Tags 03FD and 015E.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def resolutionSectionsObjIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
    [Abelian E] [HasInjectiveResolutions E]
    (S : A ⥤ B) (V : B ⥤ D) (T : A ⥤ E) (Γ : E ⥤ D)
    [S.Additive] [V.Additive] [V.PreservesHomology]
    [T.Additive] [T.PreservesHomology] [Γ.Additive] [PreservesFiniteLimits Γ]
    (q : ℕ)
    (s : (S.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      V.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q))
    {M : A} (I : InjectiveResolution M)
    (hI : ∀ n, Γ.rightAcyclic (T.obj (I.cocomplex.X n))) :
    V.obj ((S.rightDerived q).obj M) ≅ (Γ.rightDerived q).obj (T.obj M) := by
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app M ≫
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    exact quasiIso_comp _ _
  exact resolutionForgetObjIso S V I q ≪≫ s.app I.cocomplex ≪≫
    (Γ.rightDerivedObjIsoOfResolution ι hI q).symm

/-- Naturality packaged before substituting concrete chosen resolutions.
Source: Stacks Project, Tags 03FD and 015E.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def resolutionSectionsNatIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian D]
    [Abelian E] [HasInjectiveResolutions E]
    (S : A ⥤ B) (V : B ⥤ D) (T : A ⥤ E) (Γ : E ⥤ D)
    [S.Additive] [V.Additive] [V.PreservesHomology]
    [T.Additive] [T.PreservesHomology] [Γ.Additive] [PreservesFiniteLimits Γ]
    (q : ℕ)
    (s : (S.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      V.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      Γ.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q))
    (h : ∀ (M : A) [Injective M], Γ.rightAcyclic (T.obj M)) :
    S.rightDerived q ⋙ V ≅ T ⋙ Γ.rightDerived q :=
  NatIso.ofComponents
    (fun M ↦ resolutionSectionsObjIso S V T Γ q s (injectiveResolution M)
      (fun n ↦ h _)) (by
    intro M N f
    let I := injectiveResolution M
    let J := injectiveResolution N
    let hI := fun n ↦ h (I.cocomplex.X n)
    let hJ := fun n ↦ h (J.cocomplex.X n)
    let ψ : I.cocomplex ⟶ J.cocomplex := InjectiveResolution.desc f J I
    let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app M ≫
      (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
    let ι' := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app N ≫
      (T.mapHomologicalComplex (ComplexShape.up ℕ)).map J.ι
    have : QuasiIso ι := by dsimp only [ι]; exact quasiIso_comp _ _
    have : QuasiIso ι' := by dsimp only [ι']; exact quasiIso_comp _ _
    have hw : ι ≫ (T.mapHomologicalComplex _).map ψ =
        (CochainComplex.single₀ _).map (T.map f) ≫ ι' := by
      dsimp only [ι, ι']
      rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
        Functor.map_comp, ← Category.assoc]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ k ≫ (T.mapHomologicalComplex _).map J.ι)
          ((HomologicalComplex.singleMapHomologicalComplex T
            (ComplexShape.up ℕ) 0).inv.naturality f).symm
    have hc := acyclicComparison_naturality Γ ι ι' hI hJ (T.map f)
      ((T.mapHomologicalComplex _).map ψ) hw q
    have hforget : V.map ((S.rightDerived q).map f) ≫
        (resolutionForgetObjIso S V J q).hom =
          (resolutionForgetObjIso S V I q).hom ≫ HomologicalComplex.homologyMap
            ((V.mapHomologicalComplex _).map ((S.mapHomologicalComplex _).map ψ)) q := by
      dsimp only [resolutionForgetObjIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      rw [← Category.assoc, ← V.map_comp,
        InjectiveResolution.isoRightDerivedObj_hom_naturality f I J ψ
          (InjectiveResolution.desc_commutes_zero f J I) S q, V.map_comp]
      simp only [Category.assoc]
      exact congrArg (fun k ↦ V.map (I.isoRightDerivedObj S q).hom ≫ k)
        (ShortComplex.mapHomologyIso_inv_naturality
          ((HomologicalComplex.shortComplexFunctor _ _ q).map
            ((S.mapHomologicalComplex _).map ψ)) V)
    dsimp only [Functor.comp_map, resolutionSectionsObjIso, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc,
      hforget, Category.assoc]
    have hs := s.hom.naturality ψ
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hs
    simp only [Category.assoc, Iso.app_hom]
    apply congrArg (fun k ↦ (resolutionForgetObjIso S V I q).hom ≫ k)
    calc
      _ = (HomologicalComplex.homologyMap
          ((V.mapHomologicalComplex _).map ((S.mapHomologicalComplex _).map ψ)) q ≫
            s.hom.app J.cocomplex) ≫ (Γ.rightDerivedObjIsoOfResolution ι' hJ q).inv :=
        (Category.assoc _ _ _).symm
      _ = (s.hom.app I.cocomplex ≫ HomologicalComplex.homologyMap
          ((Γ.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map ψ)) q) ≫
            (Γ.rightDerivedObjIsoOfResolution ι' hJ q).inv :=
        congrArg (fun k ↦ k ≫ (Γ.rightDerivedObjIsoOfResolution ι' hJ q).inv) hs
      _ = s.hom.app I.cocomplex ≫
          (HomologicalComplex.homologyMap
            ((Γ.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map ψ)) q ≫
              (Γ.rightDerivedObjIsoOfResolution ι' hJ q).inv) := Category.assoc _ _ _
      _ = _ := congrArg (fun k ↦ s.hom.app I.cocomplex ≫ k) hc)


/-- Convert a natural comparison to an additive equivalence before specializing its functors.
Source: Stacks Project, Tags 03FD and 06XR; only categorical packaging is forgotten.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def moduleComparisonEquiv
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (M : C) : K.obj M ≃+ L.obj M :=
  (η.app M).addCommGroupIsoToAddEquiv

set_option backward.isDefEq.respectTransparency true in
private theorem moduleComparisonEquiv_naturality
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L)
    {M N : C} (f : M ⟶ N) (x : K.obj M) :
    moduleComparisonEquiv η N ((K.map f).hom x) =
      (L.map f) (moduleComparisonEquiv η M x) := by
  exact ConcreteCategory.congr_hom (η.hom.naturality f) x

end ExtEdgeResolution

/-- The coefficient comparison as a natural isomorphism of additive functors.
Source: Stacks Project, Tags 03FD, 015E and 06XR; the same common resolution.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[irreducible]
noncomputable def moduleCohomologyExtResolutionNatIso (X : Scheme.{u}) (q : ℕ) :
    RingedSpace.moduleCohomology X.toRingedSpace q ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) q := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  change (G.rightDerived q ⋙ V) ≅ T ⋙ Sheaf.functorH (Opens.grothendieckTopology X) q
  exact ExtEdgeResolution.resolutionSectionsNatIso G V T Γ q
    (ExtEdgeResolution.sectionHomologyIso X q)
    (fun M _ ↦ ExtEdgeResolution.forgottenInjectiveAcyclic X M) ≪≫
      Functor.isoWhiskerLeft T
        ((ExtEdgeResolution.siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ q).symm ≪≫
          ExtEdgeResolution.siteExtNatIso (Opens.grothendieckTopology X) ⊤ q ≪≫
            ExtEdgeResolution.extSourceNatIso (ExtEdgeResolution.terminalSourceIso X) q ≪≫
              ExtEdgeResolution.siteHNatIso (Opens.grothendieckTopology X) q)

/-- The same resolution-normalized module/Ext comparison, read from its natural square.
Its terminal-source map is Ext precomposition by the inverse of `terminalSourceIso`.
Source: Stacks Project, Tags 03FD, 015E and 06XR.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[irreducible]
def moduleCohomologyExtResolutionEquiv (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+ H F q :=
  ExtEdgeResolution.moduleComparisonEquiv (moduleCohomologyExtResolutionNatIso X q) F

set_option backward.isDefEq.respectTransparency true in
/-- The explicitly resolution-normalized comparisons are natural in coefficients.
Source: Stacks Project, Tag 03FD; Tag 015E for acyclic-resolution naturality;
Tag 06XR for Ext computed by injective resolutions.
(blueprint: new-module-cohomology-ext-resolution-naturality)

Proof: Lift the coefficient morphism to the two standard module resolutions.
The module-derived comparison commutes with this lift by isoRightDerivedObj
naturality. Exact forgetting commutes with homology by mapHomologyIso naturality.
The forgotten terms are section-acyclic by 03FD, and acyclicComparison_naturality
makes their comparison with derived abelian sections commute with the same lift.
The Hom-complex identification fromSingleEquiv commutes with postcomposition,
as does the section identification by the Yoneda and sheafification adjunctions.
Consequently the explicitly constructed Ext/derived-sections comparison commutes
with the coefficient map. Finally precomposition by terminalSourceIso commutes
with postcomposition by associativity of Ext. Compose these squares and evaluate
at x. These arguments apply in degree zero and to empty schemes and zero modules. -/
theorem moduleCohomologyExtResolutionEquiv_naturality (X : Scheme.{u}) (q : ℕ)
    (F G : X.Modules) (φ : F ⟶ G)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleCohomologyExtResolutionEquiv X G q
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
      H.map φ q (moduleCohomologyExtResolutionEquiv X F q x) := by
  unfold moduleCohomologyExtResolutionEquiv
  exact ExtEdgeResolution.moduleComparisonEquiv_naturality
    (moduleCohomologyExtResolutionNatIso X q) φ x

end AlgebraicGeometry.Scheme.Modules
