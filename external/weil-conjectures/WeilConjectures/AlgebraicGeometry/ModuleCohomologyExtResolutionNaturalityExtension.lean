/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


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
/-- Cache the sheafification proof used by the comparison on the Zariski site.
Source: Mathlib's sheafification theorem for abelian sheaves.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[instance 2000]
theorem comparisonHasSheafify (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

/-- Cache the Ext-size proof used by the comparison on the Zariski site.
Source: the Grothendieck abelian category instance for abelian sheaves.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[instance 2000]
theorem comparisonHasExt (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance

namespace ExtEdgeResolution

open CategoryTheory.Abelian CochainComplex HomComplex
section
variable {A : Type u₁} [Category.{u} A] [Abelian A] [HasExt.{u} A]
  [HasInjectiveResolutions A]


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





end





































set_option backward.isDefEq.respectTransparency true in
private theorem moduleComparisonEquiv_naturality
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L)
    {M N : C} (f : M ⟶ N) (x : K.obj M) :
    moduleComparisonEquiv η N ((K.map f).hom x) =
      (L.map f) (moduleComparisonEquiv η M x) := by
  exact ConcreteCategory.congr_hom (η.hom.naturality f) x

/-- Compose section comparisons before specializing the functors and the Ext source change.
Source: Stacks Project, Tags 03FD and 06XR; the three constructed comparison maps.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def sectionsComparisonNatIso
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q) : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ Q :=
  a ≪≫ Functor.isoWhiskerLeft T (b.symm ≪≫ c)

end ExtEdgeResolution








end AlgebraicGeometry.Scheme.Modules
