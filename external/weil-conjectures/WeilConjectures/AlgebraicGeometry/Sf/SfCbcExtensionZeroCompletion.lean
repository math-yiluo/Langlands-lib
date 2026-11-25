/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCompletionReduction
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.CategoryTheory.AdicSites.SmallSiteReducedCompletionUnit
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteEquivalenceTensor
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.Sf.SfCbcModelExtensionFlat
import WeilConjectures.AlgebraicGeometry.Sf.SfCbcModelExtensionReduction
import WeilConjectures.CategoryTheory.TowerComparisonOfUniversal

/-!
# Strict reduction of completed extension by zero

## References

* Stacks Project Tags 099M, 099N and 0941
* Stacks Project, Tags 05S7 and 06XN
* Stacks Tags 00VC and 05RU
* Stacks Tags 06YY, 0E8I and 0941
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace CategoryTheory.DerivedCategory

/-- A square of derived functors whose two computation maps are invertible on a resolving
class of complexes admits a unique comparison isomorphism normalized on that class.
The left path is an exact functor followed by a derived functor `towerX`; the right path is
a derived functor `towerU` followed by an exact functor `TD`; `c` compares the underlying
functors on complexes. -/
theorem existsUnique_iso_of_resolving
    {M C₂ C₃ C₄ D₂ H₁ H : Type*} {_ : Category M} {_ : Abelian M} {_ : HasDerivedCategory M}
    {_ : Category C₂} {_ : Category C₃} {_ : Category C₄} {_ : Category D₂} {_ : Category H₁}
    {_ : Category H}
    (ED : DerivedCategory M ⥤ D₂) (towerX : D₂ ⥤ H)
    (towerU : DerivedCategory M ⥤ H₁) (TD : H₁ ⥤ H)
    (Ec : CochainComplex M ℤ ⥤ C₂) (Q₂ : C₂ ⥤ D₂) (RX : C₂ ⥤ C₃) (TQX : C₃ ⥤ H)
    (RU : CochainComplex M ℤ ⥤ C₄) (TQU : C₄ ⥤ H₁) (Tc : C₄ ⥤ C₃)
    (EF : DerivedCategory.Q ⋙ ED ≅ Ec ⋙ Q₂) (compX : Q₂ ⋙ towerX ⟶ RX ⋙ TQX)
    (compU : DerivedCategory.Q ⋙ towerU ⟶ RU ⋙ TQU) (TF : TQU ⋙ TD ≅ Tc ⋙ TQX)
    (c : Ec ⋙ RX ≅ RU ⋙ Tc) (S : CochainComplex M ℤ → Prop)
    (hres : ∀ P : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (s : K ⟶ P), S K ∧ QuasiIso s)
    (hU : ∀ P, S P → IsIso (compU.app P)) (hX : ∀ P, S P → IsIso (compX.app (Ec.obj P))) :
    ∃! e : ED ⋙ towerX ≅ towerU ⋙ TD, ∀ P, S P →
      e.hom.app (DerivedCategory.Q.obj P) ≫ TD.map (compU.app P) ≫ TF.hom.app (RU.obj P) =
        towerX.map (EF.hom.app P) ≫ compX.app (Ec.obj P) ≫ TQX.map (c.hom.app P) := by
  let T := (RU ⋙ Tc) ⋙ TQX
  let α : DerivedCategory.Q ⋙ ED ⋙ towerX ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight EF.hom towerX ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Ec compX ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight c.hom TQX
  let β : DerivedCategory.Q ⋙ towerU ⋙ TD ⟶ T :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight compU TD ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft RU TF.hom ≫
      (Functor.associator _ _ _).inv
  have hα (P : CochainComplex M ℤ) : α.app P =
      towerX.map (EF.hom.app P) ≫ compX.app (Ec.obj P) ≫ TQX.map (c.hom.app P) := by
    simp [α]
  have hβ (P : CochainComplex M ℤ) : β.app P =
      TD.map (compU.app P) ≫ TF.hom.app (RU.obj P) := by
    simp [β]
  have hαi : ∀ P, S P → IsIso (α.app P) := by
    intro P hP
    have := hX P hP
    rw [hα]
    infer_instance
  have hβi : ∀ P, S P → IsIso (β.app P) := by
    intro P hP
    have := hU P hP
    rw [hβ]
    infer_instance
  obtain ⟨e, he⟩ := ConstantCompletion.resolving_comparison_iso _ _ T S hres α β hαi hβi
  obtain ⟨e₀, -, huniq⟩ := ConstantCompletion.resolving_comparison _ _ T S hres α β hβi
  refine ⟨e, fun P hP ↦ by rw [← hα, ← hβ]; exact he P hP, ?_⟩
  intro e₂ h₂
  apply Iso.ext
  exact (huniq e₂.hom (fun P hP ↦ by rw [hα, hβ]; exact h₂ P hP)).trans
    (huniq e.hom he).symm

end CategoryTheory.DerivedCategory

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] sfCbcConstantSliceIso constantSheaf
  sfCbcModelModules sfCbcModelRingMap sfCbcModelDerived
  SheafOfModules.monoidalCategory
  sfCbcOpenExtension sfCbcExtensionModel
attribute [-instance] sfCbcTensorTotal sfCbcSliceTransport_additive

/-- Ordinary tensor projection comparison, as one isomorphism of strict quotient diagrams.
Its equation fixes the map by the actual quotient units, not just its endpoints. -/
theorem sfCbcOrdinaryTensorComparison_existsUnique {U X : Scheme.{t}}
    (j : U ⟶ X) [IsOpenImmersion j] {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelExtension j A ⋙
        ConstantCompletion.reductionTower (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ≅
      ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ⋙ sfCbcTowerExtension j A,
      ∀ (M : ConstantCompletion.Mod (sfCbcModelRing U A)) (n : ℕ),
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology X)
            (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app
              ((sfCbcModelExtension j A).obj M)).app (op n) ≫
            (e.hom.app M).app (op n) =
          (sfCbcModelExtension j A).map
            (((ConstantCompletion.reductionUnit (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app M).app (op n)) := by
  exact Functor.existsUnique_tower_iso_of_universal (sfCbcModelExtension j A)
    (ConstantCompletion.reductionTower (proEtaleModelTopology U) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) false)
    (ConstantCompletion.reductionUnit (proEtaleModelTopology U) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) false)
    (ConstantCompletion.reductionTower (proEtaleModelTopology X) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) false)
    (ConstantCompletion.reductionUnit (proEtaleModelTopology X) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) false)
    (fun n P ↦ ConstantCompletion.IsReducedModule (proEtaleModelTopology X)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) n P)
    (fun _ _ hP ↦ hP.succ)
    (fun n N ↦ ConstantCompletion.isReducedModule_reductionTower n N)
    (fun n N P hP f ↦ ConstantCompletion.reductionUnit_existsUnique_lift n N P hP f)
    (fun n M ↦ sfCbcModelExtension_isReducedModule j d n _
      (ConstantCompletion.isReducedModule_reductionTower n M))
    (fun n M Q hQ f ↦ Functor.existsUnique_comp_map_of_adjunction
      (sfCbcModelExtensionAdjunction j A) _ Q
      (fun f' ↦ ConstantCompletion.reductionUnit_existsUnique_lift n M _
        (sfCbcModelRestriction_isReducedModule j d n Q hQ) f') f)

/-- The unique strict ordinary tensor comparison with the quotient-unit normalization. -/
def sfCbcOrdinaryTensorComparison {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :=
  (sfCbcOrdinaryTensorComparison_existsUnique j d).exists.choose

attribute [local semireducible] sfCbcModelDerived

/-- Canonical transport of the exact derived extension functor. -/
def sfCbcExtensionTransport {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    sfCbcDerivedExtension j A ⋙ (sfCbcModelDerived X A).functor ≅
      (sfCbcModelDerived U A).functor ⋙ sfCbcModelDerivedExtension j A :=
  Functor.mapDerivedCategoryCompIso (sfCbcOpenExtension j A)
      (sfCbcModelModules X A) ≪≫
    Functor.mapDerivedCategoryNatIso
      (isoWhiskerRight (sfCbcModelModules U A).asEquivalence.unitIso
        (sfCbcOpenExtension j A ⋙ sfCbcModelModules X A)) ≪≫
    (Functor.mapDerivedCategoryCompIso (sfCbcModelModules U A) (sfCbcModelExtension j A)).symm

attribute [local irreducible] sfCbcModelDerived

attribute [local irreducible] sfCbcExtensionTransport sfCbcOrdinaryTensorComparison
  ConstantCompletion.quotientPresentation sfCbcModelExtension
  NatIso.mapHomologicalComplex Functor.mapHomologicalComplexCompIso
  ConstantCompletion.reductionUnit
  ConstantCompletion.reductionTower
  sfCbcModelDerivedFactors sfCbcModelExtensionFactors sfCbcTowerExtensionFactors

/-- Normalization of the derived tensor comparison on every flat-term K-flat complex.
Both sides use the universal quotient counits and the ordinary tensor comparison. -/
def sfCbcTensorComparisonNormalized {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    (e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A) : Prop := by
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  let c : (sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ) ⋙
      (ConstantCompletion.reductionTower (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ≅
      (ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ⋙
          (sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (sfCbcOrdinaryTensorComparison j d) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := ConstantCompletion.reductionTower (proEtaleModelTopology U)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false)
        (G := sfCbcTowerExtension j A) (Iso.refl _) (.up ℤ)).symm
  exact ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
      HEq (e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
          (sfCbcDerivedTowerExtension j A).map
            ((sfCbcQuotientPresentation U d).comparison.app P) ≫
          (sfCbcTowerExtensionFactors j A).hom.app
            (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P))
        ((sfCbcQuotientPresentation X d).tower.map
            ((sfCbcModelExtensionFactors j A).hom.app P) ≫
          (sfCbcQuotientPresentation X d).comparison.app
            (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (ConstantCompletion.TQ (sfCbcModelRing X A)).map
            (c.hom.app P))

/-- The tensor projection comparison descends uniquely to derived strict towers. -/
theorem sfCbcTensorComparison_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A,
      sfCbcTensorComparisonNormalized j d e := by
  have := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  have := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  suffices key : ∀ C : (sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ) ⋙
      (ConstantCompletion.reductionTower (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ≅
      (ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ⋙
          (sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ),
      (∀ e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
          (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A,
        sfCbcTensorComparisonNormalized j d e ↔
          ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
            (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
            HEq (e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
                (sfCbcDerivedTowerExtension j A).map
                  ((sfCbcQuotientPresentation U d).comparison.app P) ≫
                (sfCbcTowerExtensionFactors j A).hom.app
                  (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
                    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P))
              ((sfCbcQuotientPresentation X d).tower.map
                  ((sfCbcModelExtensionFactors j A).hom.app P) ≫
                (sfCbcQuotientPresentation X d).comparison.app
                  (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
                (ConstantCompletion.TQ (sfCbcModelRing X A)).map (C.hom.app P))) →
      ∃! e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
        (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A,
        sfCbcTensorComparisonNormalized j d e by
    exact key _ (fun _ ↦ Iff.rfl)
  intro c hc
  let S : ConstantCompletion.Cx (sfCbcModelRing U A) → Prop :=
    fun P ↦ P.IsKFlatTensor ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)
  have hres : ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A),
      ∃ (K : ConstantCompletion.Cx (sfCbcModelRing U A)) (s : K ⟶ P), S K ∧ QuasiIso s := by
    intro P
    obtain ⟨K, s, hK, hs⟩ := ConstantCompletion.module_flat_kFlat_resolution P
    exact ⟨K, s, hK, hs⟩
  obtain ⟨e, he, huniq⟩ := DerivedCategory.existsUnique_iso_of_resolving
    (sfCbcModelDerivedExtension j A) (sfCbcQuotientPresentation X d).tower
    (sfCbcQuotientPresentation U d).tower (sfCbcDerivedTowerExtension j A)
    ((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ))
    (ConstantCompletion.Q (sfCbcModelRing X A))
    ((ConstantCompletion.reductionTower (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ))
    (ConstantCompletion.TQ (sfCbcModelRing X A))
    ((ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ))
    (ConstantCompletion.TQ (sfCbcModelRing U A))
    ((sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ))
    (sfCbcModelExtensionFactors j A) (sfCbcQuotientPresentation X d).comparison
    (sfCbcQuotientPresentation U d).comparison
    (sfCbcTowerExtensionFactors j A) c S hres
    (fun P hP ↦ (sfCbcQuotientPresentation U d).laws.2.1 P hP.1 hP.2)
    (fun P hP ↦ by
      obtain ⟨hk, hf⟩ := sfCbcModelExtension_flat_kFlat j A P hP.1 hP.2
      exact (sfCbcQuotientPresentation X d).laws.2.1 _ hk hf)
  refine ⟨e, (hc e).2 (fun P hP hf ↦ heq_of_eq (he P ⟨hP, hf⟩)), ?_⟩
  intro e₂ h₂
  exact huniq e₂ (fun P hP ↦ eq_of_heq ((hc e₂).1 h₂ P hP.1 hP.2))

attribute [local instance 1000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local semireducible] sfCbcOpenExtension

open Classical in
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local irreducible] sfCbcOpenExtension



attribute [local irreducible] adicCompletionEvaluation adicDerivedRestrict




set_option backward.isDefEq.respectTransparency true in

attribute [local instance 1000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

end AlgebraicGeometry.Scheme
