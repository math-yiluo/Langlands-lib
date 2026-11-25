/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
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
public import WeilConjectures.Algebra.Homology.LocallyFreeDerivedHom
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Derived Hom from a locally finite free module on a ringed site

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, specialized to P[0]
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).

The degree-zero formulation below is applied to every shifted bounded-below complex.
Thus H⁰ RΓ(P∨ ⊗ K[n]) is Hⁿ RΓ(P∨ ⊗ K), including negative n. The cycle normalization
specifies evaluation, rather than only asserting the existence of abstract group isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory

/-- Evaluation associated to a monoidal pairing. Source: Stacks, Tag 08JJ
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).
Factoring this formula through the ambient monoidal category keeps specialization to
sheaves from repeatedly expanding the localized associators and unitors. -/
noncomputable def locallyFreePairingEvaluate
    {A : Type*} [Category A] [MonoidalCategory A] {P D N : A}
    (ev : P ⊗ D ⟶ 𝟙_ A) (z : 𝟙_ A ⟶ D ⊗ N) : P ⟶ N :=
  (ρ_ P).inv ≫ P ◁ z ≫ (α_ P D N).inv ≫ ev ▷ N ≫ (λ_ N).hom

private theorem locallyFreeDerivedComparison_isIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) [K.IsKInjective] :
    IsIso ((locallyFreeDerivedComparison F).app K) := by
  dsimp [locallyFreeDerivedComparison]
  infer_instance

private noncomputable def pairingAddHom
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    (P D N : A) [(tensorLeft P).Additive] (ev : P ⊗ D ⟶ 𝟙_ A) :
    (𝟙_ A ⟶ D ⊗ N) →+ (P ⟶ N) where
  toFun := locallyFreePairingEvaluate ev
  map_zero' := by
    simp only [locallyFreePairingEvaluate,
      show P ◁ (0 : 𝟙_ A ⟶ D ⊗ N) = 0 from (tensorLeft P).map_zero _ _,
      comp_zero, zero_comp]
  map_add' := by
    intro a b
    simp only [locallyFreePairingEvaluate,
      show P ◁ (a + b) = P ◁ a + P ◁ b from (tensorLeft P).map_add,
      Preadditive.comp_add, Preadditive.add_comp]

private theorem pairing_eq_uncurry
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (P N : A) (z : 𝟙_ A ⟶ (ihom P).obj (𝟙_ A) ⊗ N) :
    locallyFreePairingEvaluate ((ihom.ev P).app (𝟙_ A)) z =
      (ρ_ P).inv ≫ MonoidalClosed.uncurry
        (z ≫ MonoidalClosed.ihomUnitTensorToIhom P N) := by
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.ihomUnitTensorToIhom,
    MonoidalClosed.uncurry_curry]
  rfl

private noncomputable def closedEvaluateAddEquiv
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A] [MonoidalClosed A]
    (P N : A) [(tensorLeft P).Additive]
    [IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)] :
    (𝟙_ A ⟶ (ihom P).obj (𝟙_ A) ⊗ N) ≃+ (P ⟶ N) := by
  let e := (Iso.homCongr (Iso.refl (𝟙_ A))
    (asIso (MonoidalClosed.ihomUnitTensorToIhom P N))).trans
      MonoidalClosed.curryHomEquiv'.symm
  apply AddEquiv.ofBijective
    (pairingAddHom P ((ihom P).obj (𝟙_ A)) N ((ihom.ev P).app (𝟙_ A)))
  have h : (pairingAddHom P ((ihom P).obj (𝟙_ A)) N
      ((ihom.ev P).app (𝟙_ A)) : _ → _) = e := by
    funext z
    change locallyFreePairingEvaluate _ z = _
    rw [pairing_eq_uncurry]
    simp [e, Iso.homCongr, MonoidalClosed.uncurry']
  rw [h]
  exact e.bijective

section AbstractModel

variable {A : Type v} [Category.{u} A] [Abelian A] [MonoidalCategory A]
  [MonoidalClosed A] [∀ P : A, (tensorLeft P).Additive]

private def genericGood (P : A) : Prop :=
  (∀ N, IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)) ∧
    PreservesFiniteLimits (tensorLeft P) ∧ PreservesFiniteColimits (tensorLeft P)

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericDualTensor (P : A) : A ⥤ A :=
  tensorLeft ((ihom P).obj (𝟙_ A))

/-- Additivity of the abstract model functor.
Source: Mathlib additive tensor functors and preadditive coyoneda
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
instance genericDualTensor_additive (P : A) : (genericDualTensor P).Additive := by
  dsimp [genericDualTensor]
  infer_instance

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericDualTensorMap (P P' M N : A) (p : P' ⟶ P) (f : M ⟶ N) :
    (genericDualTensor P).obj M ⟶ (genericDualTensor P').obj N :=
  tensorHom ((MonoidalClosed.pre p).app (𝟙_ A)) f

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericSections : A ⥤ AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op (𝟙_ A))

/-- Additivity of the abstract model functor.
Source: Mathlib additive tensor functors and preadditive coyoneda
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
instance genericSections_additive : (genericSections (A := A)).Additive := by
  dsimp [genericSections]
  infer_instance

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev genericTensorSections (P : A) :
    CochainComplex A ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (genericDualTensor P).mapHomologicalComplex (.up ℤ) ⋙
    genericSections.mapHomologicalComplex (.up ℤ)

/-- The abstract categorical model of this construction, specialized to sheaves below.
Source: Stacks Project, Tags 08JJ, 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def genericEvaluate (P N : A)
    (z : 𝟙_ A ⟶ (genericDualTensor P).obj N) : P ⟶ N :=
  locallyFreePairingEvaluate ((ihom.ev P).app (𝟙_ A)) z

private theorem abstract_closed_comparison_naturality
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N') :
    ((MonoidalClosed.pre p).app (𝟙_ A) ⊗ₘ f) ≫
        MonoidalClosed.ihomUnitTensorToIhom P' N' =
      MonoidalClosed.ihomUnitTensorToIhom P N ≫ (ihom P).map f ≫
        (MonoidalClosed.pre p).app N' := by
  rw [← Category.assoc (MonoidalClosed.ihomUnitTensorToIhom P N)]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_natural_left]
  simp only [MonoidalClosed.ihomUnitTensorToIhom, MonoidalClosed.uncurry_curry,
    tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, MonoidalClosed.id_tensor_pre_app_comp_ev]
  monoidal

private theorem abstract_closed_evaluation_naturality
    {A : Type*} [Category A] [MonoidalCategory A] [MonoidalClosed A]
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N')
    (g : 𝟙_ A ⟶ (ihom P).obj N) :
    (ρ_ P').inv ≫ MonoidalClosed.uncurry
        (g ≫ (ihom P).map f ≫ (MonoidalClosed.pre p).app N') =
      p ≫ (ρ_ P).inv ≫ MonoidalClosed.uncurry g ≫ f := by
  rw [← Category.assoc g, MonoidalClosed.uncurry_pre_app,
    MonoidalClosed.uncurry_natural_right]
  rw [← rightUnitor_inv_naturality_assoc]

private noncomputable def abstract_dualTensorComparison
    (P N : A) :
    (genericDualTensor P).obj N ⟶ (ihom P).obj N := by
  exact MonoidalClosed.ihomUnitTensorToIhom P N

private theorem abstract_dualTensorComparison_isIso (P N : A)
    (hP : ∀ N, IsIso (MonoidalClosed.ihomUnitTensorToIhom P N)) :
    IsIso (abstract_dualTensorComparison P N) := hP N

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_dualTensorComparison_naturality
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N') :
    genericDualTensorMap P P' N N' p f ≫ abstract_dualTensorComparison P' N' =
      abstract_dualTensorComparison P N ≫ (ihom P).map f ≫
        (MonoidalClosed.pre p).app N' := by
  exact abstract_closed_comparison_naturality P P' N N' p f

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_dualTensorMap_identity
    (P M N : A) (f : M ⟶ N) :
    genericDualTensorMap P P M N (𝟙 P) f = (genericDualTensor P).map f := by
  dsimp only [genericDualTensorMap]
  rw [MonoidalClosed.pre_id]
  exact MonoidalCategory.id_tensorHom _ f

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_evaluate_eq_uncurry
    (P N : A)
    (z : 𝟙_ A ⟶ (genericDualTensor P).obj N) :
      genericEvaluate P N z = (ρ_ P).inv ≫
      MonoidalClosed.uncurry
        (z ≫ abstract_dualTensorComparison P N) := by
  exact pairing_eq_uncurry P N z

set_option backward.isDefEq.respectTransparency false in
private theorem abstract_evaluate_naturality
    (P P' N N' : A) (p : P' ⟶ P) (f : N ⟶ N')
    (z : 𝟙_ A ⟶ (genericDualTensor P).obj N) :
    genericEvaluate P' N'
        (z ≫ genericDualTensorMap P P' N N' p f) =
      p ≫ genericEvaluate P N z ≫ f := by
  rw [abstract_evaluate_eq_uncurry, abstract_evaluate_eq_uncurry, Category.assoc,
    abstract_dualTensorComparison_naturality]
  simpa only [Category.assoc] using abstract_closed_evaluation_naturality P P' N N' p f
    (z ≫ abstract_dualTensorComparison P N)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_evaluateAddEquiv
    (P N : A) (hP : genericGood P) :
    (𝟙_ A ⟶ (genericDualTensor P).obj N) ≃+ (P ⟶ N) := by
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom P N) :=
    abstract_dualTensorComparison_isIso P N hP.1
  exact closedEvaluateAddEquiv P N

set_option backward.isDefEq.respectTransparency false in
private noncomputable def abstract_evaluationComplexIso
    (P : A)
    (hP : genericGood P)
    (K : CochainComplex (A) ℤ) :
    (genericTensorSections P).obj K ≅
      (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (abstract_evaluateAddEquiv P (K.X n) hP).toAddCommGrpIso) (by
      intro i j hij
      ext z
      symm
      change genericEvaluate P (K.X j)
        (z ≫ (genericDualTensor P).map (K.d i j)) =
          genericEvaluate P (K.X i) z ≫ K.d i j
      have h := abstract_evaluate_naturality P P (K.X i) (K.X j) (𝟙 P) (K.d i j) z
      rw [abstract_dualTensorMap_identity, Category.id_comp] at h
      exact h)

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
      simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single_obj_d])

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
  simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
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

-- Infer addition on the localized Hom group without exhausting the instance budget.
-- The cycle and naturality identities elaborate several derived Hom groups.
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

-- The cycle and naturality identities elaborate several derived Hom groups.
-- The cycle and naturality identities elaborate several derived Hom groups.
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

-- The cycle and naturality identities elaborate several derived Hom groups.
end AbstractModel

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})






set_option backward.isDefEq.respectTransparency true in
section

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]


end


variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

end CategoryTheory
