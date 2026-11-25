/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Reconstruction in the actual completed coefficient presentation

The canonical quotient transitions are the adjuncts of the quotient units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
private def reconstructionRestrictId (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

set_option backward.isDefEq.respectTransparency false in
private def reconstructionPresentationBackEquiv :
    adicDatumModules T (intrinsicPresentationDatum d) ≌ pbcModules T (pbcAdicCompletion T d) :=
  CategoryTheory.Equivalence.mk (intrinsicPresentationModulesBack T d)
    (intrinsicPresentationModules T d)
    ((pbcRestrictComp (pbcCompletedComparison T d).hom (pbcCompletedComparison T d).inv
        (𝟙 _) (pbcCompletedComparison T d).hom_inv_id ≪≫
      reconstructionRestrictId T _).symm)
    (intrinsicPresentationRoundTrip T d).symm

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
  reconstructionRestrictId

set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionStrictLimit
    (M : PbcCompletedDerived T d) (s : ℕ) (b : Fin s → A)
    (hb : Ideal.span (Set.range b) = d.ideal)
    (C : CochainComplex (adicDatumModules T (intrinsicPresentationDatum d)) ℤ)
    (eC : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison T d).inv).obj M)
    (hC : IsCompletedIntrinsicallyDerivedComplete T (intrinsicPresentationDatum d)
      s b hb C eC)
    [HasCountableProducts (reductionDerivedCategory T (completedReductionCoefficient T d))] :
    IsDerivedLimit (completedTowerDerivedStep T d ((completedReductionTower T d).obj M))
      M := by
  let G := intrinsicPresentationModules T d
  let B := intrinsicPresentationModulesBack T d
  have : B.IsEquivalence := (reconstructionPresentationBackEquiv T d).isEquivalence_functor
  let BD := B.mapDerivedCategory
  have : BD.IsEquivalence := inferInstance
  have : (pbcDerivedRestrict (pbcCompletedComparison T d).inv).IsEquivalence :=
    inferInstanceAs BD.IsEquivalence
  let adj := pbcDerivedScalarAdjunction (pbcCompletedComparison T d).inv
  have : IsIso adj.unit := by dsimp [adj]; infer_instance
  let D := (B.mapHomologicalComplex (.up ℤ)).obj C
  let eD : DerivedCategory.Q.obj D ≅ M :=
    (B.mapDerivedCategoryFactors.app C).symm ≪≫ BD.mapIso eC ≪≫
      (asIso (adj.unit.app M)).symm
  let C' := (G.mapHomologicalComplex (.up ℤ)).obj D
  let j := (reconstructionPresentationBackEquiv T d).unitIso
  let k : DerivedCategory.Q.obj C' ≅ DerivedCategory.Q.obj C :=
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex j (.up ℤ)).app C)).symm
  obtain ⟨F, η, hF⟩ := completedIntrinsicCompletion_descends T
    (intrinsicPresentationDatum d) s b
  obtain ⟨iC, hiC⟩ := hF C
  obtain ⟨iC', hiC'⟩ := hF C'
  have hu : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex T (intrinsicPresentationDatum d) s b C)) := by
    have : IsIso (eC.inv ≫ (completedConstantQ _).map
        (completedKoszulUnitComplex T (intrinsicPresentationDatum d) s b C)) := hC
    exact IsIso.of_isIso_comp_left eC.inv _
  have hη : IsIso (η.app (DerivedCategory.Q.obj C)) := by
    have : IsIso (η.app (DerivedCategory.Q.obj C) ≫ iC.hom) := by
      rw [hiC]
      exact hu
    exact IsIso.of_isIso_comp_right _ iC.hom
  have hη' : IsIso (η.app (DerivedCategory.Q.obj C')) := by
    have hn := η.naturality k.hom
    dsimp only [Functor.id_map] at hn
    have : IsIso (η.app (DerivedCategory.Q.obj C') ≫ F.map k.hom) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map k.hom)
  have hu' : IsIso ((completedConstantQ _).map
      (completedKoszulUnitComplex T (intrinsicPresentationDatum d) s b C')) := by
    rw [← hiC']
    infer_instance
  have hq : QuasiIso (completedKoszulUnitComplex T (intrinsicPresentationDatum d) s b C') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hu'
  let t : D ≅ (B.mapHomologicalComplex (.up ℤ)).obj C' :=
    (NatIso.mapHomologicalComplex (intrinsicPresentationRoundTrip T d) (.up ℤ)).app D
  have hcomp : intrinsicCompletionComplexUnit T d s b D =
      t.hom ≫ (B.mapHomologicalComplex (.up ℤ)).map
        (completedKoszulUnitComplex T (intrinsicPresentationDatum d) s b C') := by
    unfold intrinsicCompletionComplexUnit intrinsicCompletionUnitComponent
    ext q
    rfl
  have hDC : QuasiIso (intrinsicCompletionComplexUnit T d s b D) := by
    rw [hcomp]
    infer_instance
  have hQu : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d s b D)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hDC
  have hD : IsDerivedCompleteIntrinsic T d s b hb M D eD := by
    unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit intrinsicCompletion
    exact IsIso.comp_isIso' eD.isIso_inv hQu
  have : IsIso (intrinsicCompletionUnit T d s b hb M D eD) := hD
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d s b hb M D eD
  let e := asIso (intrinsicCompletionUnit T d s b hb M D eD) ≪≫ c
  obtain ⟨δ, hδ⟩ := completedRlim_roos T d ((completedReductionTower T d).obj M)
  let p := completedRlimRoosProjection T d ((completedReductionTower T d).obj M)
  refine ⟨e.hom ≫ p, δ ≫ (shiftFunctor _ (1 : ℤ)).map e.inv, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  exact Pretriangulated.Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    (by simp [p]) (by simp) (by simp)

private theorem reconstructionUnit_section
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction φ).unit.app M).val.app U x = pbcTensorSection φ M U 1 x :=
  (pbcScalarAdjunction_exists φ).exists.choose_spec M U x

private theorem reconstructionComp_section
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M U x

attribute [local irreducible] pbcScalarAdjunction pbcRestrictComp

section ScalarComputation
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
  (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

private theorem reconstructionTranspose
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (N : CochainComplex (pbcModules T S) ℤ)
    (k : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ N) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _
        (pbcComplexCounit φ P ≫ DerivedCategory.Q.map k) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app N =
      DerivedCategory.Q.map (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv
        P N k) := by
  change ((pbcDerivedScalarAdjunction φ).unit.app _ ≫
    (pbcDerivedRestrict φ).map (pbcComplexCounit φ P ≫ DerivedCategory.Q.map k)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  erw [(pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality k]
  simp only [Functor.comp_map] at *
  have hu := (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec P hP
  change (pbcDerivedScalarAdjunction φ).unit.app _ ≫
    (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫ _ = _ at hu
  erw [reassoc_of% hu]
  rw [← DerivedCategory.Q.map_comp]
  rfl

private theorem reconstructionRestrictionFactors
    (N : CochainComplex (pbcModules T B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).hom.app (DerivedCategory.Q.obj N) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app N =
      (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj N) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app N) := by
  dsimp only [pbcDerivedRestrictComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac]
  have hc := Functor.mapDerivedCategoryCompIso_fac (pbcRestrict ψ) (pbcRestrict φ) N
  have hi : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pbcRestrict ψ ⋙ pbcRestrict φ)) (.up ℤ)).hom.app N = 𝟙 _ := by
    ext i
    rfl
  rw [hi] at hc
  erw [DerivedCategory.Q.map_id, Category.comp_id] at hc
  rw [← hc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

private def reconstructionOrdinaryTransition (M : pbcModules T R) :
    (pbcExtend φ).obj M ⟶ (pbcRestrict ψ).obj ((pbcExtend χ).obj M) :=
  ((pbcScalarAdjunction φ).homEquiv _ _).symm
    ((pbcScalarAdjunction χ).unit.app M ≫
      (pbcRestrictComp φ ψ χ h).inv.app ((pbcExtend χ).obj M))

private theorem reconstructionOrdinaryTransition_unit (M : pbcModules T R) :
    (pbcScalarAdjunction φ).unit.app M ≫
        (pbcRestrict φ).map (reconstructionOrdinaryTransition T φ ψ χ h M) ≫
        (pbcRestrictComp φ ψ χ h).hom.app ((pbcExtend χ).obj M) =
      (pbcScalarAdjunction χ).unit.app M := by
  rw [← Category.assoc]
  change ((pbcScalarAdjunction φ).homEquiv _ _
    (reconstructionOrdinaryTransition T φ ψ χ h M)) ≫ _ = _
  rw [reconstructionOrdinaryTransition, Equiv.apply_symm_apply]
  simp

private theorem reconstructionRestrictionFactors_inv
    (N : CochainComplex (pbcModules T B) ℤ) :
    (pbcDerivedRestrictComp φ ψ χ h).inv.app (DerivedCategory.Q.obj N) ≫
        (pbcDerivedRestrict φ).map ((pbcRestrict ψ).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj N) =
      (pbcRestrict χ).mapDerivedCategoryFactors.hom.app N ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).inv (.up ℤ)).app N) := by
  apply (cancel_epi ((pbcDerivedRestrictComp φ ψ χ h).hom.app
    (DerivedCategory.Q.obj N))).1
  simp only [Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% (reconstructionRestrictionFactors T φ ψ χ h)]
  simp only [← DerivedCategory.Q.map_comp]
  have hi : ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app N) ≫
      ((NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).inv (.up ℤ)).app N) = 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (pbcRestrictComp φ ψ χ h).hom_inv_id_app _
  rw [hi, DerivedCategory.Q.map_id]
  erw [Category.comp_id]

private def reconstructionOrdinaryTransitionNat :
    pbcExtend φ ⟶ pbcExtend χ ⋙ pbcRestrict ψ where
  app := reconstructionOrdinaryTransition T φ ψ χ h
  naturality {M N} f := by
    apply ((pbcScalarAdjunction φ).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    simp only [reconstructionOrdinaryTransition, Equiv.apply_symm_apply]
    have hn := (pbcRestrictComp φ ψ χ h).inv.naturality ((pbcExtend χ).map f)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [← hn]
    have hu := (pbcScalarAdjunction χ).unit.naturality f
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ (pbcRestrictComp φ ψ χ h).inv.app ((pbcExtend χ).obj N)) hu

private theorem reconstructionTransition_computation
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P) ≫
        (pbcDerivedRestrict ψ).map (pbcComplexCounit χ P) ≫
        (pbcRestrict ψ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      pbcComplexCounit φ P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (reconstructionOrdinaryTransitionNat T φ ψ χ h) (.up ℤ)).app P) := by
  apply ((pbcDerivedScalarAdjunction φ).homEquiv _ _).injective
  apply (cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app
    (((pbcRestrict ψ).mapHomologicalComplex (.up ℤ)).obj
      (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P)))).1
  erw [reconstructionTranspose T φ P hP]
  simp only [Adjunction.homEquiv_naturality_right, pbcReductionTransition,
    Equiv.apply_symm_apply, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ((pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    (pbcComplexCounit χ P))]
  erw [reconstructionRestrictionFactors_inv T φ ψ χ h]
  have hu := (pbcDerivedScalarAdjunction_exists χ).exists.choose_spec P hP
  change (pbcDerivedScalarAdjunction χ).unit.app _ ≫
    (pbcDerivedRestrict χ).map (pbcComplexCounit χ P) ≫ _ = _ at hu
  erw [reassoc_of% hu]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  apply HomologicalComplex.Hom.ext
  funext i
  change _ = ((pbcScalarAdjunction φ).unit.app (P.X i) ≫
    (pbcRestrict φ).map (reconstructionOrdinaryTransition T φ ψ χ h (P.X i)))
  change _ = (pbcScalarAdjunction φ).homEquiv _ _
    (reconstructionOrdinaryTransition T φ ψ χ h (P.X i))
  rw [reconstructionOrdinaryTransition, Equiv.apply_symm_apply]
  rfl

private theorem reconstructionRestrictedTransition_computation
    (P : CochainComplex (pbcModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    ((pbcDerivedRestrict φ).map (pbcReductionTransition φ ψ χ h (DerivedCategory.Q.obj P)) ≫
      (pbcDerivedRestrictComp φ ψ χ h).hom.app
        ((pbcDerivedExtend χ).obj (DerivedCategory.Q.obj P))) ≫
        (pbcDerivedRestrict χ).map (pbcComplexCounit χ P) ≫
        (pbcRestrict χ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (reconstructionOrdinaryTransitionNat T φ ψ χ h) (.up ℤ)).app P) ≫
            (NatTrans.mapHomologicalComplex (pbcRestrictComp φ ψ χ h).hom (.up ℤ)).app
              (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P)) := by
  simp only [Category.assoc]
  rw [← reassoc_of% ((pbcDerivedRestrictComp φ ψ χ h).hom.naturality
    (pbcComplexCounit χ P))]
  erw [reconstructionRestrictionFactors T φ ψ χ h]
  simp only [← Functor.map_comp_assoc]
  rw [reconstructionTransition_computation T φ ψ χ h P hP]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [(pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map, DerivedCategory.Q.map_comp]

end ScalarComputation

private theorem reconstructionOrdinaryTensor
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (((pbcRestrict φ).map (reconstructionOrdinaryTransition T φ ψ χ h M) ≫
      (pbcRestrictComp φ ψ χ h).hom.app ((pbcExtend χ).obj M)).val.app U)
        (pbcTensorSection φ M U s x) =
      pbcTensorSection χ M U (ψ.hom.app U s) x := by
  let g := reconstructionOrdinaryTransition T φ ψ χ h M
  have hunit := reconstructionOrdinaryTransition_unit T φ ψ χ h M
  have hg : g.val.app U (pbcTensorSection φ M U 1 x) =
      pbcTensorSection χ M U 1 x := by
    have hh := congrArg (fun k ↦ k.val.app U x) hunit
    change ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
      (g.val.app U (((pbcScalarAdjunction φ).unit.app M).val.app U x)) =
      ((pbcScalarAdjunction χ).unit.app M).val.app U x at hh
    rw [show ((pbcScalarAdjunction φ).unit.app M).val.app U x =
        pbcTensorSection φ M U 1 x from
      reconstructionUnit_section T φ M U x,
      show ((pbcScalarAdjunction χ).unit.app M).val.app U x =
        pbcTensorSection χ M U 1 x from
      reconstructionUnit_section T χ M U x] at hh
    erw [show ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
        (g.val.app U (pbcTensorSection φ M U 1 x)) =
        g.val.app U (pbcTensorSection φ M U 1 x) from
      reconstructionComp_section T φ ψ χ h _ U _] at hh
    exact hh
  change ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
      (g.val.app U (pbcTensorSection φ M U s x)) = _
  rw [show ((pbcRestrictComp φ ψ χ h).hom.app _).val.app U
      (g.val.app U (pbcTensorSection φ M U s x)) =
      g.val.app U (pbcTensorSection φ M U s x) from
    reconstructionComp_section T φ ψ χ h _ U _]
  rw [show pbcTensorSection φ M U s x = s • pbcTensorSection φ M U 1 x by
    simpa only [pbcTensorSection, reductionTensorSection, pbcExtend, reductionChange,
      mul_one] using (tensorSection_smul T φ M U s 1 x).symm]
  rw [map_smul, hg]
  change ψ.hom.app U s • pbcTensorSection χ M U 1 x = _
  simpa only [pbcTensorSection, reductionTensorSection, pbcExtend, reductionChange,
    mul_one] using tensorSection_smul T χ M U (ψ.hom.app U s) 1 x

private theorem reconstructionOrdinaryStep (b a : ℕ) (hab : a ≤ b)
    (M : pbcModules T (pbcAdicCompletion T d)) :
    (pbcRestrict (pbcAdicProjection T d b)).map
        (reconstructionOrdinaryTransition T (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) M) ≫
        (pbcRestrictComp (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
          (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab)).hom.app
            ((pbcExtend (pbcAdicProjection T d a)).obj M) =
      (completedReductionTransition T d b a hab).app M := by
  apply level_hom_ext T (pbcAdicProjection T d b) M
  intro U s x
  exact (reconstructionOrdinaryTensor T (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
    (pbcAdicProjection_comp T d b a hab) M U s x).trans
      ((completedReductionTransition_exists T d b a hab).exists.choose_spec M U s x).symm

private theorem reconstructionTransition_natural
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K L : DerivedCategory (pbcModules T R)} (f : K ⟶ L) :
    (pbcDerivedExtend φ).map f ≫ pbcReductionTransition φ ψ χ h L =
      pbcReductionTransition φ ψ χ h K ≫
        (pbcDerivedRestrict ψ).map ((pbcDerivedExtend χ).map f) := by
  let a := pbcDerivedScalarAdjunction φ
  apply (a.homEquiv K _).injective
  dsimp only [pbcReductionTransition]
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  have hn := (pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    ((pbcDerivedExtend χ).map f)
  dsimp only [Functor.comp_map] at hn
  have hu := (pbcDerivedScalarAdjunction χ).unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hn, ← Category.assoc, hu, Category.assoc]

private def reconstructionStep (n : ℕ) :
    pbcCompletedReduction T d (n + 1) ⋙
        pbcDerivedRestrict (pbcAdicProjection T d (n + 1)) ⟶
      pbcCompletedReduction T d n ⋙ pbcDerivedRestrict (pbcAdicProjection T d n) where
  app K := (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
    (pbcReductionTransition (pbcAdicProjection T d (n + 1))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
      (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
      (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
        ((pbcCompletedReduction T d n).obj K)
  naturality {K L} f := by
    dsimp only [Functor.comp_map]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [reconstructionTransition_natural T]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
      (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.naturality
        ((pbcCompletedReduction T d n).map f)
    dsimp only [Functor.comp_map] at hn
    rw [hn]

private def reconstructionStrictStep (n : ℕ) :
    completedReductionTower T d ⋙ reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) (n + 1) ⟶
      completedReductionTower T d ⋙ reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) n :=
  Functor.whiskerLeft (completedReductionTower T d)
    (Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ _
      (reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) (n + 1))
      (reductionTowerDerivedEvaluation T
        (reductionModuleRing T (completedReductionCoefficient T d)) n)
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
        (reductionModuleRing T (completedReductionCoefficient T d)) n) (.up ℤ))
          DerivedCategory.Q))

private theorem reconstructionStep_comparison (n : ℕ) :
    reconstructionStrictStep T d n ≫ completedReductionEvaluation T d n =
      completedReductionEvaluation T d (n + 1) ≫ reconstructionStep T d n := by
  apply derived_natTrans_ext _ _
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P)
    (fun X ↦ by
      obtain ⟨P, p, hk, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients
          (R := completedReductionCoefficient T d) X
      exact ⟨P, p, hk, hp⟩)
  intro P hP
  let φ := pbcAdicProjection T d n
  let c := (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
    (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
  have : IsIso (pbcComplexCounit φ P) := scalarCounit_isIso T φ P hP
  have : IsIso c := by dsimp [c]; infer_instance
  apply (cancel_mono c).1
  simp only [NatTrans.comp_app, Category.assoc]
  have he (i : ℕ) :=
    (completedReductionEvaluation_exists T d i).choose_spec.1.2 P hP
  have hs := reconstructionRestrictedTransition_computation T
    (pbcAdicProjection T d (n + 1))
    (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) φ
    (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) P hP
  let J := (completedReductionComplexTowerFunctor T d).obj P
  let q := completedReductionTowerComplexCounit T d P
  let E (i : ℕ) := reductionTowerDerivedEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) i
  let F (i : ℕ) := reductionTowerEvaluation T
    (reductionModuleRing T (completedReductionCoefficient T d)) i
  let τ := Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ (E (n + 1)) (E n)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
      (reductionModuleRing T (completedReductionCoefficient T d)) n) (.up ℤ))
        DerivedCategory.Q)
  let t := (NatTrans.mapHomologicalComplex (completedTowerEvaluationStep T
    (reductionModuleRing T (completedReductionCoefficient T d)) n) (.up ℤ)).app J
  have ht : τ.app (DerivedCategory.Q.obj J) ≫ (F n).mapDerivedCategoryFactors.hom.app J =
      (F (n + 1)).mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map t := by
    dsimp only [τ]
    erw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Functor.whiskerRight_app, Category.assoc]
    dsimp only [F, t]
    simp only [Iso.inv_hom_id_app, Category.comp_id]
  have hj :
      (((pbcRestrict (pbcAdicProjection T d (n + 1))).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (reconstructionOrdinaryTransitionNat T (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) φ
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))) (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex (pbcRestrictComp (pbcAdicProjection T d (n + 1))
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) φ
          (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom (.up ℤ)).app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)) = t := by
    apply HomologicalComplex.Hom.ext
    funext i
    dsimp only [φ, t, J, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, reconstructionOrdinaryTransitionNat,
      Functor.mapHomologicalComplex_obj_X, completedTowerEvaluationStep,
      completedReductionComplexTowerFunctor, completedReductionModuleTowerFunctor,
      completedReductionModuleTower]
    simp only [Functor.ofOpSequence_map_homOfLE_succ]
    exact reconstructionOrdinaryStep T d (n + 1) n (Nat.le_succ n) (P.X i)
  rw [hj] at hs
  simp only [Category.assoc] at hs
  dsimp only [reconstructionStrictStep, Functor.whiskerLeft_app]
  change τ.app _ ≫ (completedReductionEvaluation T d n).app _ ≫ c =
    (completedReductionEvaluation T d (n + 1)).app _ ≫
      (reconstructionStep T d n).app _ ≫ c
  dsimp only [c]
  erw [he n]
  change _ = (completedReductionEvaluation T d (n + 1)).app _ ≫
    (((pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map _) ≫ _) ≫ _
  simp only [Category.assoc]
  erw [hs]
  erw [reassoc_of% (he (n + 1))]
  have hn := τ.naturality q
  change τ.app _ ≫ (E n).map q ≫ (F n).mapDerivedCategoryFactors.hom.app J = _
  rw [← Category.assoc, ← hn, Category.assoc, ht]

private theorem reconstructionLimit_transport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : ℕ → C} [HasProduct X] [HasProduct Y]
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (L : C) (hL : IsDerivedLimit f L) (a : ∀ n, X n ≅ Y n)
    (ha : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n) :
    IsDerivedLimit g L := by
  obtain ⟨p, δ, hδ⟩ := hL
  let E : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨p ≫ E.hom, E.inv ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl L) E.symm E.symm ?_ ?_ ?_
  · change (p ≫ E.hom) ≫ E.inv = 𝟙 L ≫ p
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ha n))).symm
  · change (E.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 L) = E.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- An intrinsically complete object is a Roos limit of its actual quotient reductions.
Source: blueprint order 1270, Koszul reconstruction; Stacks Tags 091N and 0DVC.
(blueprint: lem-weil-pbc-actual-completed-reduction-reconstruction).

Proof: choose a K-flat representative in the constant completed-ring presentation
used to define intrinsic completeness. The completed Koszul reduction Roos triangle
identifies its intrinsic completion with the derived limit of its strict quotient
tower. The completeness hypothesis makes the completion map invertible, so transport
that triangle's first vertex to the given object. Transport the coefficient ring
along pbcCompletedComparison. This exact equivalence preserves countable products,
so it preserves the Roos triangle. At each finite level the normalized constant
quotient comparison identifies the transported tower with the actual quotient
extension followed by scalar restriction. The tensor-unit normalization makes the
adjacent square commute: both adjuncts are the direct quotient unit. The product of
these level isomorphisms conjugates the transition endomorphisms. Transporting the
two product vertices therefore gives the displayed distinguished Roos triangle.
No bound, constructibility, flatness, or choice of a limit functor is needed. -/
theorem pbc_actual_completed_reduction_reconstruction
    [HasCountableProducts (PbcCompletedDerived T d)]
    (K : PbcCompletedDerived T d) (hK : PbcIsIntrinsicallyComplete T d K) :
    let M : ℕᵒᵖ ⥤ PbcCompletedDerived T d :=
    Functor.ofOpSequence
        (X := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
          ((pbcCompletedReduction T d n).obj K))
        (fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
          (pbcReductionTransition (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
          (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
              ((pbcCompletedReduction T d n).obj K))
    IsDerivedLimit
      (K := fun n ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op) K := by
  dsimp only
  simp only [Functor.ofOpSequence_obj, Functor.ofOpSequence_map_homOfLE_succ]
  obtain ⟨s, b, hb, C, eC, hC⟩ := hK
  have : HasCountableProducts
      (reductionDerivedCategory T (completedReductionCoefficient T d)) :=
    inferInstanceAs (HasCountableProducts (PbcCompletedDerived T d))
  apply reconstructionLimit_transport _ _ K
    (reconstructionStrictLimit T d K s b hb C eC hC)
    (fun n ↦ (asIso (completedReductionEvaluation T d n)).app K)
  intro n
  simpa only [reconstructionStrictStep, reconstructionStep, completedTowerDerivedStep,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.app_hom, asIso_hom, Category.assoc] using
      congr_app (reconstructionStep_comparison T d n) K

end AlgebraicGeometry.Scheme
