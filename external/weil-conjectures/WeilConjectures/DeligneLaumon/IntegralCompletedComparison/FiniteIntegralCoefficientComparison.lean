/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.IntegralCompletedComparison.IntegralPullbackCompletedComparisonData
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

set_option linter.privateModule false

/-! # Finite integral coefficient pullback normalization

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-finite-integral-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

private abbrev completedCoeff (W : Scheme.{u}) :=
  ImmersionCompletedPullback.completedRingIso l E W

private abbrev finiteCoeff (W : Scheme.{u}) (n : ℕ) :=
  ImmersionCompletedPullback.finiteRingIso l E W n

private theorem projection_square (W : Scheme.{u}) (n : ℕ) :
    (completedCoeff l E W).inv ≫ pbcAdicProjection W (pbcIntegralDatum l E) n =
      completedIntegralCommRingProjectionUnrestricted l E W n ≫
        (finiteCoeff l E W n).inv := by
  have h := (ImmersionCompletedPullback.completedRingIso_exists l E W).exists.choose_spec n
  change (completedCoeff l E W).hom ≫ _ = _ at h
  apply (cancel_mono (finiteCoeff l E W n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.inv_hom_id_assoc]

private def restrictionSquare (W : Scheme.{u}) (n : ℕ) :=
  (IntegralCoefficientPresentation.restrictionSquare
    (completedCoeff l E W).inv (pbcAdicProjection W (pbcIntegralDatum l E) n)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (finiteCoeff l E W n).inv (projection_square l E W n)).symm

private def integralAdj (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralReductionFunctor.{u, u} l E W n ⊣
      scalarReductionRestriction.{u, u} l E W n :=
  (scalarReductionExtension_adjunction.{u, u} l E W n).choose

private theorem reductionComparison_exists (W : Scheme.{u}) (n : ℕ) :
    ∃ a : modules l E W ⋙ unrestrictedIntegralReductionFunctor.{u, u} l E W n ≅
        reductionChange W (pbcAdicProjection W (pbcIntegralDatum l E) n) ⋙
          pbcRestrict (finiteCoeff l E W n).inv,
      ∀ M, (integralAdj l E W n).unit.app ((modules l E W).obj M) ≫
        (scalarReductionRestriction.{u, u} l E W n).map (a.hom.app M) ≫
        (restrictionSquare l E W n).hom.app
          ((reductionChange W (pbcAdicProjection W (pbcIntegralDatum l E) n)).obj M) =
        (modules l E W).map
          ((pbcScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n)).unit.app M) := by
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (completedCoeff l E W)).2.1
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (finiteCoeff l E W n)).2.1
  exact IntegralCoefficientPresentation.square_iso (integralAdj l E W n)
    (pbcScalarAdjunction (pbcAdicProjection W (pbcIntegralDatum l E) n))
    (modules l E W) (pbcRestrict (finiteCoeff l E W n).inv)
    (restrictionSquare l E W n)

private def finiteStructure (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E Y n) ≅
      integralCoefficientCommRingSheaf l E X n :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso
      (finiteCoeff l E Y n).symm ≪≫
    asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n) ≪≫
      finiteCoeff l E X n

private theorem finiteStructure_hom (n : ℕ) :
    (finiteStructure l E g n).hom =
      proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  apply (cancel_epi ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
    (finiteCoeff l E Y n).hom)).1
  dsimp only [finiteStructure, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  symm
  dsimp only [finiteCoeff, ImmersionCompletedPullback.finiteRingIso,
    completedFiniteCoefficientMap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun z ↦ (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
    (pbcLevelConstantComparison Y (pbcIntegralDatum l E) n).inv ≫ z)
      (proEtaleConstantInverseImageMap_naturality g
        (ImmersionCompletedPullback.quotientEquiv l E n).toCommRingCatIso.hom)

private theorem finiteDirect_eq (n : ℕ) :
    proEtaleRingModuleDirectImage g (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (finiteStructure l E g n) =
      coefficientProEtaleModuleDirectImage.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  unfold proEtaleRingModuleDirectImage proEtaleRingDirectImageMap
  rw [finiteStructure_hom]
  change SheafOfModules.pushforward _ = SheafOfModules.pushforward _
  congr 1
  apply Sheaf.hom_ext
  change Functor.whiskerRight _ _ = Functor.whiskerRight _ _
  congr 1
  apply congrArg (fun z : integralCoefficientCommRingSheaf l E Y n ⟶
    (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (integralCoefficientCommRingSheaf l E X n) ↦ z.hom)
  exact ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

private theorem finiteStructure_square (n : ℕ) :
    (finiteStructure l E g n).hom ≫ (finiteCoeff l E X n).inv =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (finiteCoeff l E Y n).inv ≫
          (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n)).hom := by
  simp only [finiteStructure, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def finiteDirectSquare (n : ℕ) :=
  proEtaleRingRestrictionDirectImage g
    (integralCoefficientCommRingSheaf l E Y n) (reductionCoefficient Y (pbcIntegralDatum l E) n)
    (integralCoefficientCommRingSheaf l E X n) (reductionCoefficient X (pbcIntegralDatum l E) n)
    (finiteCoeff l E Y n).inv (finiteCoeff l E X n).inv
    (finiteStructure l E g n)
    (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))
    (finiteStructure_square l E g n)

private def pullbackRightSquare (n : ℕ) :=
  Functor.isoWhiskerLeft (pbcRestrict (finiteCoeff l E X n).inv)
      (eqToIso (finiteDirect_eq l E g n)).symm ≪≫
    (finiteDirectSquare l E g n).symm

private theorem pullbackComparison_exists (n : ℕ) :
    ∃ b : pbcRestrict (finiteCoeff l E Y n).inv ⋙ integralOperationsLevelPullback l E g n ≅
        completedReductionFiniteModules g (pbcIntegralDatum l E) n ⋙
          pbcRestrict (finiteCoeff l E X n).inv,
      ∀ M,
        (coefficientProEtaleModuleAdjunction.{u, u} g
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
            ((pbcRestrict (finiteCoeff l E Y n).inv).obj M) ≫
          (coefficientProEtaleModuleDirectImage.{u, u} g
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).map
              (b.hom.app M) ≫
          (pullbackRightSquare l E g n).hom.app
            ((completedReductionFiniteModules g (pbcIntegralDatum l E) n).obj M) =
          (pbcRestrict (finiteCoeff l E Y n).inv).map
            ((proEtaleRingModuleAdjunction g _ _
              (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n))).unit.app M) := by
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (finiteCoeff l E Y n)).2.1
  have := (IntegralCoefficientPresentation.restrict_equivalence
    (finiteCoeff l E X n)).2.1
  exact IntegralCoefficientPresentation.square_iso
    (coefficientProEtaleModuleAdjunction.{u, u} g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (proEtaleRingModuleAdjunction g _ _
      (asIso (completedFiniteCoefficientMap g (pbcIntegralDatum l E) n)))
    (pbcRestrict (finiteCoeff l E Y n).inv) (pbcRestrict (finiteCoeff l E X n).inv)
    (pullbackRightSquare l E g n)

private def reductionComparison (W : Scheme.{u}) (n : ℕ) :=
  (reductionComparison_exists l E W n).choose

private def pullbackComparison (n : ℕ) := (pullbackComparison_exists l E g n).choose

private def finalRestrictionSquare (n : ℕ) :=
  IntegralCoefficientPresentation.restrictionSquare
    (completedIntegralCommRingProjectionUnrestricted l E X n) (finiteCoeff l E X n).inv
    (completedCoeff l E X).inv (pbcAdicProjection X (pbcIntegralDatum l E) n)
    (projection_square l E X n).symm

private def comparison (n : ℕ) : finiteIntegral l E g n ≅ finiteCompleted l E g n :=
  Functor.isoWhiskerRight (reductionComparison l E Y n)
      (integralOperationsLevelPullback l E g n ⋙
        pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E X n)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reductionChange Y (pbcAdicProjection Y (pbcIntegralDatum l E) n))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pullbackComparison l E g n)
          (pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E X n)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (completedReductionFiniteModules g (pbcIntegralDatum l E) n)
          (finalRestrictionSquare l E (X := X) n)) ≪≫
    (Functor.associator _ _ _).symm

attribute [local irreducible] pbcIntegralDatum reductionComparison pullbackComparison

end WeilConjectures.IntegralCompletedComparison
