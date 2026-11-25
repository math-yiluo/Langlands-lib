/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.DualTensorHomComparison
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Free
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Derived Hom from a locally finite free module on a ringed site

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, specialized to P[0]
(auxiliary; not a blueprint node).

The degree-zero formulation below is applied to every shifted bounded-below complex.
Thus H⁰ RΓ(P∨ ⊗ K[n]) is Hⁿ RΓ(P∨ ⊗ K), including negative n. The cycle normalization
specifies evaluation, rather than only asserting the existence of abstract group isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory

/-- The ordinary-to-derived zeroth-cohomology comparison for an additive functor.
Source: Stacks, Tags 0A8Z and 08JA
(auxiliary; not a blueprint node). -/
noncomputable def locallyFreeDerivedComparison
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor B (.up ℤ) 0 ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B 0 := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let a : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso B)).inv ≫
    Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) F.rightDerivedFunctor).hom
  exact (Functor.isoWhiskerLeft G (DerivedCategory.homologyFunctorFactors B 0)).inv ≫
    Functor.whiskerRight a (DerivedCategory.homologyFunctor B 0)

private theorem locallyFreeDerivedComparison_isIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) [K.IsKInjective] :
    IsIso ((locallyFreeDerivedComparison F).app K) := by
  dsimp [locallyFreeDerivedComparison]
  infer_instance

section AbstractModel

variable {A : Type v} [Category.{u} A] [Abelian A] [MonoidalCategory A]
  [MonoidalClosed A] [∀ P : A, (tensorLeft P).Additive]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_singleHomComplexIso
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor A 0).obj P) K ≅
      (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := P) (K := K) (zero_add n)).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ :=
          CochainComplex.HomComplex.Cochain.fromSingleMk_surjective a i (zero_add i)
        change CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add i)
            (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)) ≫ K.d i j =
          CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add j)
            (CochainComplex.HomComplex.δ i j
              (CochainComplex.HomComplex.Cochain.fromSingleMk a (zero_add i)))
        simp only [CochainComplex.HomComplex.Cochain.δ_fromSingleMk, zero_add,
          CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk])

private noncomputable def abstract_singleHomologyEquiv
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ) :
    ((((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).homology 0) ≃+
      ((HomotopyCategory.quotient A (.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj P) ⟶
          (HomotopyCategory.quotient A (.up ℤ)).obj K) :=
  let e := HomologicalComplex.homologyMapIso (abstract_singleHomComplexIso P K).symm 0
  e.addCommGroupIsoToAddEquiv.trans
    ((CochainComplex.HomComplex.leftHomologyData _ K 0).homologyIso.addCommGroupIsoToAddEquiv.trans
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
        (Linear.homCongr ℤ (Iso.refl _)
          ((HomotopyCategory.quotient A (.up ℤ)).mapIso
            ((shiftFunctorZero _ ℤ).app K))).toAddEquiv))

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_singleHomologyEquiv_cycle
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ)
    (z : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).cycles 0)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ K)
    (hf : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
      ((((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).iCycles 0) z) :
    abstract_singleHomologyEquiv P K
      (HomologicalComplex.homologyπ
        (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) 0 z) =
      (HomotopyCategory.quotient A (.up ℤ)).map f := by
  let S := (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K)
  let E := abstract_singleHomComplexIso P K
  let D := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor A 0).obj P) K 0
  let y := HomologicalComplex.cyclesMap E.inv 0 z
  have hy : D.cyclesIso.hom y = CochainComplex.HomComplex.Cocycle.ofHom f := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ))).injective
    have h₁ : (D.cyclesIso.hom y).val =
        (((CochainComplex.singleFunctor A 0).obj P).HomComplex K).iCycles 0 y :=
      ConcreteCategory.congr_hom D.cyclesIso_hom_comp_i y
    have h₂ : (((CochainComplex.singleFunctor A 0).obj P).HomComplex K).iCycles 0 y =
        E.inv.f 0 (S.iCycles 0 z) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i E.inv 0) z
    rw [h₁.trans h₂]
    change (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ)))
      ((CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add (0 : ℤ))).symm
        (S.iCycles 0 z)) = _
    rw [AddEquiv.apply_symm_apply]
    simpa [S, CochainComplex.HomComplex.Cochain.fromSingleEquiv] using hf.symm
  have hπ : HomologicalComplex.homologyMap E.inv 0 (S.homologyπ 0 z) =
      (((CochainComplex.singleFunctor A 0).obj P).HomComplex K).homologyπ 0 y :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality E.inv 0) z
  have hD : D.homologyIso.hom
      ((((CochainComplex.singleFunctor A 0).obj P).HomComplex K).homologyπ 0 y) =
      CochainComplex.HomComplex.CohomologyClass.mk (D.cyclesIso.hom y) :=
    ConcreteCategory.congr_hom D.homologyπ_comp_homologyIso_hom y
  unfold abstract_singleHomologyEquiv
  change (Linear.homCongr ℤ (Iso.refl _)
      ((HomotopyCategory.quotient A (.up ℤ)).mapIso
        ((shiftFunctorZero _ ℤ).app K))).toAddEquiv
    (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (D.homologyIso.hom (HomologicalComplex.homologyMap E.inv 0 (S.homologyπ 0 z)))) = _
  rw [hπ, hD, hy]
  change (𝟙 _ ≫ (HomotopyCategory.quotient A (.up ℤ)).map
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.ofHom f))) ≫
    (HomotopyCategory.quotient A (.up ℤ)).map
      ((shiftFunctorZero _ ℤ).hom.app K) = _
  rw [Category.id_comp, ← Functor.map_comp]
  congr 1
  ext
  simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.homOf, CochainComplex.HomComplex.Cocycle.rightShift,
    CochainComplex.HomComplex.Cochain.rightShift_v, CochainComplex.shiftFunctorZero_hom_app_f]

private instance abstract_addCommGrpForgetSelf :
    HasForget₂ AddCommGrpCat.{u} AddCommGrpCat.{u} where
  forget₂ := 𝟭 _
  forget_comp := rfl

private instance abstract_addCommGrpForgetSelf_additive :
    (forget₂ AddCommGrpCat.{u} AddCommGrpCat.{u}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u}).Additive

private instance abstract_addCommGrpForgetSelf_homology :
    (forget₂ AddCommGrpCat.{u} AddCommGrpCat.{u}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u}).PreservesHomology

private noncomputable def abstract_singleMapCycle
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ K) :
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).cycles 0 :=
  (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).cyclesMk (i := 0)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) 1 (by simp) (by
      change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) ≫ K.d 0 1 = 0
      erw [Category.assoc, f.comm]
      simp [CochainComplex.singleFunctor, HomologicalComplex.single_obj_d])

private theorem abstract_singleMapCycle_i
    {A : Type*} [Category A] [Abelian A] (P : A) (K : CochainComplex A ℤ)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ K) :
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).iCycles 0
      (abstract_singleMapCycle P K f) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 := by
  unfold abstract_singleMapCycle
  exact HomologicalComplex.i_cyclesMk
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_singleHomologyEquiv_naturality
    {A : Type*} [Category A] [Abelian A] (P P' : A) (K L : CochainComplex A ℤ)
    (p : P' ⟶ P) (f : K ⟶ L)
    (t : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (((preadditiveCoyoneda.obj (op P')).mapHomologicalComplex (.up ℤ)).obj L))
    (ht : ∀ (i : ℤ) (a : P ⟶ K.X i), t.f i a = p ≫ a ≫ f.f i)
    (x : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).homology 0) :
    abstract_singleHomologyEquiv P' L (HomologicalComplex.homologyMap t 0 x) =
      (HomotopyCategory.quotient A (.up ℤ)).map
        ((CochainComplex.singleFunctor A 0).map p) ≫
          abstract_singleHomologyEquiv P K x ≫ (HomotopyCategory.quotient A (.up ℤ)).map f := by
  let S := (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K)
  let S' := (((preadditiveCoyoneda.obj (op P')).mapHomologicalComplex (.up ℤ)).obj L)
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨g, hg⟩ := q.map_surjective (abstract_singleHomologyEquiv P K x)
  let z := abstract_singleMapCycle P K g
  have hz : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ g.f 0 =
      S.iCycles 0 z := (abstract_singleMapCycle_i P K g).symm
  have hx : x = S.homologyπ 0 z :=
    (abstract_singleHomologyEquiv P K).injective
      (hg.symm.trans (abstract_singleHomologyEquiv_cycle P K z g hz).symm)
  rw [hx]
  have hπ : HomologicalComplex.homologyMap t 0 (S.homologyπ 0 z) =
      S'.homologyπ 0 (HomologicalComplex.cyclesMap t 0 z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t 0) z
  rw [hπ, abstract_singleHomologyEquiv_cycle P K z g hz]
  rw [← q.map_comp, ← q.map_comp]
  apply abstract_singleHomologyEquiv_cycle
  have hi : S'.iCycles 0 (HomologicalComplex.cyclesMap t 0 z) = t.f 0 (S.iCycles 0 z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t 0) z
  rw [hi, ht, ← hz]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [← Category.assoc (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P').inv]
  simp [CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self, Category.assoc]

variable [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{u} A]

private noncomputable def abstract_kInjectiveQuotientEquiv
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P K : CochainComplex A ℤ) [K.IsKInjective] :
    ((HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj K) ≃+
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K) :=
  (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
    (CochainComplex.IsKInjective.Qh_map_bijective _ K)).trans
      (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso A).app P)
        ((DerivedCategory.quotientCompQhIso A).app K)).toAddEquiv

private theorem abstract_kInjectiveQuotientEquiv_map
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P K : CochainComplex A ℤ) [K.IsKInjective] (f : P ⟶ K) :
    abstract_kInjectiveQuotientEquiv P K ((HomotopyCategory.quotient A (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  change (((DerivedCategory.quotientCompQhIso A).app P).inv ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f)) ≫
      ((DerivedCategory.quotientCompQhIso A).app K).hom = _
  rw [Category.assoc]
  erw [(DerivedCategory.quotientCompQhIso A).hom.naturality f]
  simp

private theorem abstract_kInjectiveQuotientEquiv_naturality
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P P' : CochainComplex A ℤ) (K L : CochainComplex A ℤ)
    [K.IsKInjective] [L.IsKInjective] (p : P' ⟶ P) (f : K ⟶ L)
    (a : (HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj K) :
    abstract_kInjectiveQuotientEquiv P' L
      ((HomotopyCategory.quotient A (.up ℤ)).map p ≫ a ≫
        (HomotopyCategory.quotient A (.up ℤ)).map f) =
      DerivedCategory.Q.map p ≫ abstract_kInjectiveQuotientEquiv P K a ≫
        DerivedCategory.Q.map f := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective a
  rw [← Functor.map_comp, ← Functor.map_comp, abstract_kInjectiveQuotientEquiv_map,
    abstract_kInjectiveQuotientEquiv_map, Functor.map_comp, Functor.map_comp]

private noncomputable def locallyFreeResolution :
    CochainComplex (A) ℤ ⥤
    CochainComplex (A) ℤ := by
  exact CochainComplex.kInjectiveResolutionFunctor.{u} A

private noncomputable def locallyFreeResolutionUnit :
    𝟭 (CochainComplex (A) ℤ) ⟶
        locallyFreeResolution := by
  exact CochainComplex.toKInjectiveResolution.{u} A

private instance abstract_resolution_isKInjective
    (K : CochainComplex (A) ℤ) :
    ((locallyFreeResolution).obj K).IsKInjective := by
  exact CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A K

private instance abstract_resolution_unit_quasiIso
    (K : CochainComplex (A) ℤ) :
    QuasiIso ((locallyFreeResolutionUnit).app K) := by
  exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A K).2

end AbstractModel

end CategoryTheory
