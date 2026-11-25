/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
import all WeilConjectures.CategoryTheory.DirectImageRoosNormalization.DirectImageRoosNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor

/-!
# The canonical direct-image/derived-limit comparison

Source: blueprint proper base change, direct image and limits; Stacks Tag 099N
and Cohomology on Sites, lemma-Rf-commutes-with-Rlim
(blueprint: proposition-proper-base-change-complete-integral--1).

## Main statements

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Dependent scalar-extension proofs should not be replayed by tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- The ordinary direct image on strict towers applies the actual module functor levelwise.
Source: blueprint direct image and limits (blueprint:
proposition-proper-base-change-complete-integral--1). -/
abbrev AdicCoefficientDatum.towerModulePush : d.towers U ⥤ d.towers V :=
  (Functor.whiskeringRight _ _ _).obj
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))

/-- Direct image of strict towers is additive termwise.
Source: blueprint direct image and limits (blueprint:
proposition-proper-base-change-complete-integral--1). -/
instance AdicCoefficientDatum.towerModulePush_additive :
    (d.towerModulePush f).Additive := inferInstance

/-- The canonical termwise module adjunction on strict towers.
Source: blueprint direct image and limits (blueprint:
proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.towerModuleAdjunction :
    d.towerModulePull f ⊣ d.towerModulePush f :=
  (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)).whiskerRight ℕᵒᵖ

/-- The total right derived direct image in the abelian category of strict towers.
Source: blueprint direct image and limits (blueprint:
proposition-proper-base-change-complete-integral--1). -/
abbrev AdicCoefficientDatum.towerPush := (d.towerModulePush f).rightDerivedFunctor

/-- The derived tower adjunction comes from its canonical ordinary adjunction.
Source: blueprint direct image and limits (blueprint:
proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.towerAdjunction : d.towerPull f ⊣ d.towerPush f :=
  (d.towerModuleAdjunction f).mapDerivedCategoryRightDerivedAdjunction

private theorem evaluationMapKInjective
    (B : Type*) [Category B] [Abelian B]
    (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective] (n : ℕᵒᵖ) :
    CochainComplex.IsKInjective
      ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj J) :=
  tower_evaluation_isKInjective B J n

private theorem evaluationPreservesKInjective (B : Type*) [Category B] [Abelian B]
    (n : ℕᵒᵖ) : ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).PreservesKInjectiveComplexes :=
  ⟨fun J _ ↦ evaluationMapKInjective B J n⟩

/-- Evaluation of strict towers preserves K-injective complexes: its left adjoint
is the exact sum of copies indexed by arrows into the chosen level.
Source: blueprint direct image and limits, evaluation clause; Stacks 079P
(blueprint: proposition-proper-base-change-complete-integral--1).
Proof: the left adjoint is left Kan extension from the one-object subcategory.
Its values are sums of copies indexed by arrows into the evaluation index. These
sums are exact in the Grothendieck module category. Adjunction transports maps from
acyclic complexes to null-homotopic maps into the given K-injective tower. -/
@[instance]
theorem completedTowerEvaluation_kinjective (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) (n : ℕ)
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((reductionTowerEvaluation T (reductionModuleRing T R) n).mapHomologicalComplex
        (.up ℤ)).obj J) := by
  exact evaluationMapKInjective _ J (Opposite.op n)

set_option linter.defProp false in
/-- The exact K-injective normalization of tower direct-image evaluation.
Source: blueprint direct image and limits, evaluation clause; Stacks 099N
(blueprint: proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.IsTowerPushEvaluation (n : ℕ)
    (α : d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
        reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
          d.push f) : Prop :=
  ∀ (J : CochainComplex (d.towers U) ℤ) [J.IsKInjective],
        (reductionTowerDerivedEvaluation V
            (reductionModuleRing V (d.completedRing V)) n).map
            ((d.towerModulePush f).rightDerivedFunctorObjQIso J).hom ≫
          (reductionTowerEvaluation V
            (reductionModuleRing V (d.completedRing V)) n).mapDerivedCategoryFactors.hom.app
              (((d.towerModulePush f).mapHomologicalComplex (.up ℤ)).obj J) =
        α.hom.app (DerivedCategory.Q.obj J) ≫
          (d.push f).map ((reductionTowerEvaluation U
            (reductionModuleRing U (d.completedRing U)) n).mapDerivedCategoryFactors.hom.app J) ≫
          ((proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
            (d.integralRingIso f)).rightDerivedFunctorObjQIso
              (((reductionTowerEvaluation U
                (reductionModuleRing U (d.completedRing U)) n).mapHomologicalComplex
                  (.up ℤ)).obj J)).hom

private theorem quotientHomId {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 (DerivedCategory.Q.obj J) := rfl

private theorem quotientInvId {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app J = 𝟙 (DerivedCategory.Q.obj J) := rfl

private theorem homotopyFactorsInvId {B C : Type*} [Category B] [Category C]
    [Abelian B] [Abelian C] (F : B ⥤ C) [F.Additive] (J : CochainComplex B ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl

section NormalizedTowerEvaluation
attribute [local instance] evaluationPreservesKInjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedTowerEvaluation
    (B C : Type*) [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (G : B ⥤ C) [G.Additive] (n : ℕᵒᵖ) :
    let F := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
    let EU := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
    let EV := (CategoryTheory.evaluation ℕᵒᵖ C).obj n
    ∃! e : F.rightDerivedFunctor ⋙ EV.mapDerivedCategory ≅
        EU.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
        EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
          EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
        e.hom.app (DerivedCategory.Q.obj J) ≫
          G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
            (G.rightDerivedFunctorObjQIso ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
  let F := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
  let EU := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  let EV := (CategoryTheory.evaluation ℕᵒᵖ C).obj n
  have : EU.PreservesKInjectiveComplexes := ⟨fun J _ ↦
    tower_evaluation_isKInjective B J n⟩
  let α := Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F EV
  let β := Functor.mapDerivedCategoryCompRightDerivedFunctorUnit EU G
  let e := Functor.rightDerivedUnique (F.rightDerivedFunctor ⋙ EV.mapDerivedCategory)
    (EU.mapDerivedCategory ⋙ G.rightDerivedFunctor) α β
    (HomotopyCategory.quasiIso ((ℕᵒᵖ ⥤ B)) (.up ℤ))
  have he : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
      EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      e.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
    intro J hJ
    have hh : α ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom = β := by
      simp [e]
    have h := NatTrans.congr_app hh ((HomotopyCategory.quotient _ _).obj J)
    dsimp only [α, β, Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_map] at h
    simp only [Category.id_comp, Category.comp_id, Category.assoc] at h
    have hEV : EV.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ _).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj J)) =
        EV.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj J) := by
      apply Iso.ext
      have hv := EV.mapDerivedCategoryFactorsh_hom_app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)
      rw [quotientHomId, quotientInvId, homotopyFactorsInvId] at hv
      erw [EV.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
        Category.id_comp, Category.comp_id] at hv
      erw [Category.comp_id] at hv
      exact hv
    have hEU : EU.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ _).obj J) = EU.mapDerivedCategoryFactors.app J := by
      apply Iso.ext
      have hu := EU.mapDerivedCategoryFactorsh_hom_app J
      rw [quotientHomId, quotientInvId, homotopyFactorsInvId] at hu
      erw [EU.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
        Category.id_comp, Category.comp_id] at hu
      erw [Category.comp_id] at hu
      exact hu
    have hidF : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ EV)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ _).obj J) = 𝟙 _ := rfl
    have hidG : (Functor.mapHomotopyCategoryCompIso (Iso.refl (EU ⋙ G)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ _).obj J) = 𝟙 _ := rfl
    rw [hidF, hidG] at h
    erw [DerivedCategory.Qh.map_id, Category.id_comp, Category.id_comp] at h
    change EV.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj J)) ≫
        EV.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj J)) ≫ e.hom.app (DerivedCategory.Q.obj J) =
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((EU.mapHomologicalComplex (.up ℤ)).obj J)) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj J)) at h
    change (EV.mapDerivedCategoryFactorsh.app _).inv ≫ _ =
      _ ≫ G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactorsh.app _).inv at h
    erw [hEV, hEU] at h
    let qα := (EV.mapDerivedCategoryFactors.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).symm ≪≫
      EV.mapDerivedCategory.mapIso (asIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj J)))
    let qβ := asIso (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((EU.mapHomologicalComplex (.up ℤ)).obj J))) ≪≫
      G.rightDerivedFunctor.mapIso (EU.mapDerivedCategoryFactors.app J).symm
    have hh' : qα.hom ≫ e.hom.app (DerivedCategory.Q.obj J) = qβ.hom := by
      simpa only [qα, qβ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        asIso_hom, Category.assoc] using h
    have hh'' := congrArg (fun k ↦ qα.inv ≫ k ≫ qβ.inv) hh'
    have hfinal : qα.inv = e.hom.app (DerivedCategory.Q.obj J) ≫ qβ.inv := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using hh''.symm
    change EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      e.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso
            ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom
    dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_inv]
    simp only [quotientHomId, quotientInvId, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_comp, Category.id_comp]
    erw [EV.mapDerivedCategory.map_id, Category.comp_id]
    erw [Category.comp_id]
    simpa only [qα, qβ, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
      Iso.app_inv, Functor.mapIso_inv, asIso_inv, Category.assoc] using hfinal
  refine ⟨e, he, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext M
  obtain ⟨J, hJ, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have := hJ
  have h := (ha J).symm.trans (he J)
  have hi : a.hom.app (DerivedCategory.Q.obj J) =
      e.hom.app (DerivedCategory.Q.obj J) := by
    exact (cancel_mono _).1 h
  apply (cancel_epi ((F.rightDerivedFunctor ⋙ EV.mapDerivedCategory).map i.inv)).1
  rw [a.hom.naturality, e.hom.naturality, hi]

end NormalizedTowerEvaluation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The levelwise direct image comparison is fixed on K-injective towers by the
identity of the two termwise evaluations. It is a natural isomorphism.
Source: blueprint direct image and limits, first clause; Stacks 099N
(blueprint: proposition-proper-base-change-complete-integral--1).
Proof: evaluation preserves K-injectives by its exact left adjoint. Thus each side
is computed by evaluating the same termwise direct image of a K-injective tower.
The two factorization maps and universal derived units give the displayed equation.
It descends through localization; every tower has such a resolution, so the equation
uniquely specifies the natural comparison. -/
theorem AdicCoefficientDatum.towerPushEvaluation_existsUnique (n : ℕ) :
    ∃! α : d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
        reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
          d.push f,
      d.IsTowerPushEvaluation f n α := by
  exact normalizedTowerEvaluation
    (ringedSiteModules.{t + 1} (reductionModuleRing U (d.completedRing U)))
    (ringedSiteModules.{t + 1} (reductionModuleRing V (d.completedRing V)))
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (Opposite.op n)

/-- The canonical tower direct-image evaluation comparison, retaining its model equation.
Source: blueprint direct image and limits (blueprint:
proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.towerPushEvaluation (n : ℕ) :
    d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
      reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
        d.push f :=
  (d.towerPushEvaluation_existsUnique f n).choose

/-- The canonical comparison is the conjugate of the identity constant/pullback square.
It is therefore the comparison of the two composite right adjoints, including their units.
No arbitrary isomorphism of the resulting objects is chosen.
Source: blueprint direct image and limits; lemma-Rf-commutes-with-Rlim
(blueprint: proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.directImageRlimIso :
    completedRlim U (d.completedRing U) ⋙ d.push f ≅
      d.towerPush f ⋙ completedRlim V (d.completedRing V) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).comp (d.constantRlimAdjunction U))
    ((d.constantRlimAdjunction V).comp (d.towerAdjunction f))
    (d.derivedConstantPullbackIso f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] CategoryTheory.towerNormalization_preservesFiniteLimits
  CategoryTheory.towerNormalization_preservesFiniteColimits

private theorem evaluationSquare_inverse
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    (P : C ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (n : ℕᵒᵖ) :
    (Functor.mapDerivedCategoryCompIso ((CategoryTheory.evaluation ℕᵒᵖ C).obj n) P ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ C B).obj P)
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)).symm).hom =
    (Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ C B).obj P)
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n) ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      (Functor.mapDerivedCategoryCompIso
        ((CategoryTheory.evaluation ℕᵒᵖ C).obj n) P).symm).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.refl_symm,
    Functor.mapDerivedCategoryNatIso_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryEvaluation_mate
    {B C : Type*} [Category B] [Category C]
    {L : C ⥤ B} {R : B ⥤ C} (adj : L ⊣ R) (n : ℕᵒᵖ) :
    (mateEquiv (adj.whiskerRight ℕᵒᵖ) adj
      (TwoSquare.mk ((CategoryTheory.evaluation ℕᵒᵖ C).obj n)
        ((Functor.whiskeringRight ℕᵒᵖ C B).obj L) L
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj n) (𝟙 _))) =
      𝟙 (((Functor.whiskeringRight ℕᵒᵖ B C).obj R) ⋙ (CategoryTheory.evaluation ℕᵒᵖ C).obj n) := by
  ext M
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, NatTrans.id_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp]
  erw [R.map_id, Category.id_comp, Category.comp_id]
  change adj.unit.app (R.obj (M.obj n)) ≫
    R.map (((adj.whiskerRight ℕᵒᵖ).counit.app M).app n) = 𝟙 _
  rw [Adjunction.whiskerRight_counit_app_app]
  exact adj.right_triangle_components _

attribute [local instance] evaluationPreservesKInjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluationComparison_mate
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (P : C ⥤ B) (G : B ⥤ C) [P.Additive] [G.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (adj : P ⊣ G) (n : ℕᵒᵖ)
    (β : ((Functor.whiskeringRight ℕᵒᵖ B C).obj G).rightDerivedFunctor ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hβ : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B C).obj G).rightDerivedFunctorObjQIso J).hom ≫
        ((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B C).obj G).mapHomologicalComplex (.up ℤ)).obj J) =
      β.hom.app (DerivedCategory.Q.obj J) ≫ G.rightDerivedFunctor.map
        (((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app J) ≫
      (G.rightDerivedFunctorObjQIso
        ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj J)).hom) :
    β.hom = (mateEquiv (adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
      adj.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ C B).obj P)
          ((CategoryTheory.evaluation ℕᵒᵖ B).obj n) ≪≫
          Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
          (Functor.mapDerivedCategoryCompIso ((CategoryTheory.evaluation ℕᵒᵖ C).obj n) P).symm).inv
        )) := by
  let F := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
  let EU := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  let EV := (CategoryTheory.evaluation ℕᵒᵖ C).obj n
  let H := (Functor.whiskeringRight ℕᵒᵖ C B).obj P
  have : EU.PreservesKInjectiveComplexes := evaluationPreservesKInjective B n
  let e : F ⋙ EV ≅ EU ⋙ G := Iso.refl _
  let q : EV ⋙ P ≅ H ⋙ EU := Iso.refl _
  let c := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F EV).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso EU G ≪≫
      Functor.isoWhiskerRight EU.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
  have hc : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
      EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      c.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
    intro J hJ
    have h :=
      AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_normalized
        F EU EV G e J
    change c.hom.app (DerivedCategory.Q.obj J) ≫ _ ≫ _ = _ ≫ _ ≫
      DerivedCategory.Q.map (𝟙 _) at h
    erw [DerivedCategory.Q.map_id, Category.comp_id] at h
    exact h.symm
  have heq : c = β := (normalizedTowerEvaluation B C G n).unique hc hβ
  apply (congrArg Iso.hom heq).symm.trans
  have hm := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_eq_mate
    F EU EV G H P (adj.whiskerRight ℕᵒᵖ) adj q e (ordinaryEvaluation_mate adj n)
  rw [hm]
  exact congrArg (fun k ↦ (mateEquiv
    (adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    adj.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ k)))
    (evaluationSquare_inverse P n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerPushEvaluation_mate (n : ℕ) :
    (d.towerPushEvaluation f n).hom =
      (mateEquiv (d.towerAdjunction f)
        (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f))
        (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)) := by
  exact evaluationComparison_mate
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
    (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (op n) (d.towerPushEvaluation f n)
    (d.towerPushEvaluation_existsUnique f n).choose_spec.1

universe w
private def constantEvaluationIso
    (B : Type*) [Category B] [Abelian B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] (n : ℕᵒᵖ) :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.constCompEvaluationObj (D := B) n) ≪≫
      Functor.mapDerivedCategoryIdIso _

private theorem constantEvaluation_factors
    (B : Type*) [Category B] [Abelian B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (n : ℕᵒᵖ) (J : CochainComplex B ℤ) :
    (constantEvaluationIso B n).hom.app (DerivedCategory.Q.obj J) =
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app J) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app
        (((Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)).obj J) := by
  let D := (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B))
  let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  change (Functor.mapDerivedCategoryCompIso D E).hom.app (DerivedCategory.Q.obj J) ≫
    (Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 B))).hom.app (DerivedCategory.Q.obj J) ≫
      (Functor.mapDerivedCategoryIdIso B).hom.app (DerivedCategory.Q.obj J) = _
  rw [Functor.mapDerivedCategoryNatIso_refl]
  simp only [NatTrans.id_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app]
  have hi : (Functor.mapHomologicalComplexIdIso B (.up ℤ)).hom.app J = 𝟙 _ := rfl
  rw [hi]
  erw [DerivedCategory.Q.map_id, Category.comp_id]
  have h := Functor.mapDerivedCategoryCompIso_hom_app_factors D E J
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso D E).inv.app
    (DerivedCategory.Q.obj J))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]
  exact h.symm

private theorem derivedCounit_unit
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    {L : B ⥤ C} {R : C ⥤ B} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (J : CochainComplex C ℤ) :
    L.mapDerivedCategory.map
        (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj J) =
    L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app J) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj J)
  erw [AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom L
    ((R.mapHomologicalComplex (.up ℤ)).obj J)] at h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  exact h

private theorem constantLimit_projection_unit
    (B : Type*) [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (n : ℕᵒᵖ) (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj J) ≫
      (constantEvaluationIso B n).inv.app
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.obj (DerivedCategory.Q.obj J)) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        (((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim)
          ).mapDerivedCategoryRightDerivedAdjunction.counit.app
            (DerivedCategory.Q.obj J)) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app J) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app J := by
  let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  let C : B ⥤ (ℕᵒᵖ ⥤ B) := Functor.const ℕᵒᵖ
  let L : (ℕᵒᵖ ⥤ B) ⥤ B := lim
  let adj := (constLimAdj : C ⊣ L).mapDerivedCategoryRightDerivedAdjunction
  let e := constantEvaluationIso B n
  let unit := L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)
  have hc := derivedCounit_unit (constLimAdj : C ⊣ L) J
  have hn := e.inv.naturality unit
  change unit ≫ e.inv.app _ = e.inv.app _ ≫ E.mapDerivedCategory.map
    (C.mapDerivedCategory.map unit) at hn
  change unit ≫ (e.inv.app _ ≫ E.mapDerivedCategory.map _) = _
  rw [← Category.assoc, hn, Category.assoc, ← E.mapDerivedCategory.map_comp]
  rw [hc]
  rw [E.mapDerivedCategory.map_comp]
  rw [← Category.assoc]
  have hf := constantEvaluation_factors B n ((L.mapHomologicalComplex (.up ℤ)).obj J)
  have he : e.inv.app _ ≫ E.mapDerivedCategory.map
      (C.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J)) =
    E.mapDerivedCategoryFactors.inv.app
      ((C.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj J)) := by
    apply (cancel_mono (E.mapDerivedCategoryFactors.hom.app _)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hf]
    exact e.inv_hom_id_app _
  erw [he]
  exact (E.mapDerivedCategoryFactors.inv.naturality
    (((constLimAdj : C ⊣ L).mapHomologicalComplex (.up ℤ)).counit.app J)).symm

private def limitCounitProjection (T : Scheme.{t}) (n : ℕ) :
    completedRlim T (d.completedRing T) ⟶
      reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n where
  app M := (constantEvaluationIso (reductionModules T (d.completedRing T)) (op n)).inv.app
      ((completedRlim T (d.completedRing T)).obj M) ≫
    (reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n).map
      ((d.constantRlimAdjunction T).counit.app M)
  naturality M N a := by
    let E := reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n
    let L := completedRlim T (d.completedRing T)
    let C := d.derivedConstantTower T
    let e := constantEvaluationIso (reductionModules T (d.completedRing T)) (op n)
    have hn := e.inv.naturality (L.map a)
    change L.map a ≫ e.inv.app (L.obj N) =
      e.inv.app (L.obj M) ≫ E.map (C.map (L.map a)) at hn
    change L.map a ≫ (e.inv.app (L.obj N) ≫ E.map _) =
      (e.inv.app (L.obj M) ≫ E.map _) ≫ E.map a
    rw [← Category.assoc, hn, Category.assoc, ← E.map_comp]
    erw [(d.constantRlimAdjunction T).counit.naturality]
    simp only [E.map_comp, Category.assoc, Functor.id_map]

private theorem limitCounitProjection_unit (T : Scheme.{t}) (n : ℕ)
    (J : CochainComplex (d.towers T) ℤ) :
    (completedRlimUnit T (d.completedRing T)).app ((HomotopyCategory.quotient _ _).obj J) ≫
      (limitCounitProjection d T n).app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app J) ≫
      (reductionTowerEvaluation T (reductionModuleRing T
        (d.completedRing T)) n).mapDerivedCategoryFactors.inv.app J := by
  exact constantLimit_projection_unit (reductionModules T (d.completedRing T)) (op n) J

private theorem limitCounitProjection_eq (T : Scheme.{t}) (n : ℕ) :
    limitCounitProjection d T n = completedRlimProjection T (d.completedRing T) n := by
  apply NatTrans.ext
  funext M
  obtain ⟨J, hJ, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have := hJ
  have : IsIso ((completedRlimUnit T (d.completedRing T)).app
      ((HomotopyCategory.quotient _ _).obj J)) := completedRlim_computation T _ J
  have hj : (limitCounitProjection d T n).app (DerivedCategory.Q.obj J) =
      (completedRlimProjection T (d.completedRing T) n).app (DerivedCategory.Q.obj J) := by
    apply (cancel_epi ((completedRlimUnit T (d.completedRing T)).app
      ((HomotopyCategory.quotient _ _).obj J))).mp
    exact (limitCounitProjection_unit d T n J).trans
      (completedRlimProjection_unit T (d.completedRing T) J n).symm
  apply (cancel_epi ((completedRlim T (d.completedRing T)).map i.inv)).mp
  rw [(limitCounitProjection d T n).naturality,
    (completedRlimProjection T (d.completedRing T) n).naturality, hj]

universe ub vb uc vc
attribute [local instance] evaluationPreservesKInjective

/-- The ordinary scalar/pullback mate, in the inverse direction of chi.
Source: blueprint four corners and tower compatibility; Stacks 06YY and 0D6D
(blueprint: proposition-proper-base-change-complete-integral--1). -/
def completedOrdinaryReductionPullbackInv (n : ℕ) :
    proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ proEtaleRingExtension (d.projection U n) ⟶
      proEtaleRingExtension (d.projection V n) ⋙
        proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (d.projection V n))
    (proEtaleRingExtensionAdjunction (d.projection U n))).symm
      (proEtaleRingRestrictionPullbackInv f (d.completedRing V) (d.finiteRing V n)
        (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
          (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized ordinary mate is the invertible tensor balancing map.
Source: blueprint tower compatibility; Stacks 03EL and 06YY
(blueprint: proposition-proper-base-change-complete-integral--1).
Proof: the tensor-unit normalized adjunctions compute this mate on pure tensors.
It sends the inverse image of m tensored with p to the inverse image of m tensor p.
The coefficient projection square makes the map quotient-linear. The reverse tensor
reassociation is inverse, as checked on pure tensors and then on sheafifications. -/
theorem completedOrdinaryReductionPullbackInv_isIso (n : ℕ) :
    IsIso (completedOrdinaryReductionPullbackInv d f n) := by
  let av := proEtaleRingExtensionAdjunction (d.projection V n)
  let au := proEtaleRingExtensionAdjunction (d.projection U n)
  let ar := proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let az := proEtaleRingModuleAdjunction f (d.finiteRing V n) (d.finiteRing U n)
    (d.finiteRingIso f n)
  let b := proEtaleRingRestrictionPullbackInv f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let c := proEtaleRingRestrictionDirectImage f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let α := TwoSquare.mk _ _ _ _ b
  have hm : mateEquiv az ar α = TwoSquare.mk _ _ _ _ c.hom := by
    rw [← Equiv.eq_symm_apply]
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [α, b, mateEquiv_symm_apply, proEtaleRingRestrictionPullbackInv,
      proEtaleRingRestrictionPullbackApp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
      Category.id_comp]
    simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
    dsimp only [Functor.comp_obj]
    simp only [Category.id_comp]
    exact (Category.comp_id _).symm
  let γ := (mateEquiv av au).symm α
  have hγ : mateEquiv av au γ = α := (mateEquiv av au).apply_symm_apply α
  have : IsIso (conjugateEquiv (av.comp az) (ar.comp au) γ) := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az γ, hγ, hm]
    change IsIso c.hom
    infer_instance
  change IsIso γ
  exact conjugateEquiv_of_iso (av.comp az) (ar.comp au) γ

attribute [instance] completedOrdinaryReductionPullbackInv_isIso

/-- The ordinary reduction-level comparison after restriction to completed coefficients.
Source: blueprint tower compatibility (blueprint:
proposition-proper-base-change-complete-integral--1). -/
def completedReductionLevelPullbackIso (n : ℕ) :
    completedReductionLevel V d n ⋙
        proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ completedReductionLevel U d n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (d.projection V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
        (d.projection V n) (d.projection U n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
          (d.projection V n) (d.projection U n) (d.integralRingIso f)
          (d.finiteRingIso f n) (d.projection_comm f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (completedOrdinaryReductionPullbackInv d f n)).symm
      (proEtaleRingRestrictScalars (d.projection U n)) ≪≫
    Functor.associator _ _ _

section TowerPullTransition
attribute [local irreducible] pbcScalarAdjunction proEtaleRingModuleAdjunction
set_option backward.isDefEq.respectTransparency false

private theorem restrictionPullback_unit
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aV ≫ cS.hom)
    (N : proEtaleRingModules V SV) (W : V.ProEtᵒᵖ) (z : N.val.obj W) :
    ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app N).val.app
        ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f RV RU cR).unit.app
          ((proEtaleRingRestrictScalars aV).obj N)).val.app W z) =
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z := by
  let δ := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let σ := proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm
  have h := unit_mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR) (TwoSquare.mk _ _ _ _ σ) N
  have hm := restrictionPullback_mate f RV SV RU SU aV aU cR cS comm
  change (proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N) ≫
        (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
          (proEtaleRingModuleAdjunction f RV RU cR)
          (TwoSquare.mk _ _ _ _ σ)).app _ = _ at h
  rw [hm] at h
  have hz := congrArg (fun k ↦ k.val.app W z) h
  change (δ.hom.app ((proEtaleRingModulePullback f SV SU cS).obj N)).val.app W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z) = _ at hz
  have he := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)).1
      ((proEtaleRingModulePullback f SV SU cS).obj N) W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z)
  exact (he.symm.trans hz).symm

end TowerPullTransition

section GenericComparisonPredicate
variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  (F : B ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] (G : C ⥤ (ℕᵒᵖ ⥤ C)) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ C)) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (e : F ⋙ H ≅ P ⋙ G)
  (LF : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
  (LG : DerivedCategory C ⥤ DerivedCategory (ℕᵒᵖ ⥤ C))
  (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

end GenericComparisonPredicate

set_option linter.defProp false in
/-- Reuse the strict quotient-unit normalized representative formula.
The ordinary comparison agrees with this module's by `ordinaryReduction_eq_stratum`.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: proposition-proper-base-change-complete-integral--1). -/
def IsCompletedReductionPullbackComparison
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d) : Prop :=
  StratumReductionFormula d f τ

attribute [local semireducible] completedReductionCoefficient

private theorem reductionFormula_iff
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower U d) :
    IsCompletedReductionPullbackComparison d f τ ↔ StratumReductionFormula d f τ := Iff.rfl

/-- The universal normalization of the ordinary reduction comparison determines its derived lift.
Source: Stacks Tags 06YY and 03EL
(blueprint: proposition-proper-base-change-complete-integral--1).
Proof: the quotient-unit normalization identifies the ordinary comparison with the strict
stratum comparison. Their representative formulas are identical. Existence and uniqueness
therefore follow from the normalized strict reduction comparison. -/
theorem completedReductionPullbackIso_existsUnique :
    ∃! τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d,
      IsCompletedReductionPullbackComparison d f τ := by
  obtain ⟨τ, hτ, hu⟩ := stratumReductionIso_exists d f
  exact ⟨τ, (reductionFormula_iff d f τ).mpr hτ,
    fun η hη ↦ hu η ((reductionFormula_iff d f η).mp hη)⟩

/-- The normalized reduction-tower/pullback isomorphism, rather than an arbitrary lift
of levelwise maps. Source: blueprint tower compatibility
(blueprint: proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.reductionTowerPullbackIso :
    completedReductionTower V d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower U d :=
  (completedReductionPullbackIso_existsUnique d f).choose

/-- The strict derived projection map is the adjunct of tower chi followed by the
reduction of the ambient counit. Its evaluation is the specified finite projection.
Source: blueprint tower compatibility (blueprint:
proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.towerProjection (K : d.derived U) :
    (completedReductionTower V d).obj ((d.push f).obj K) ⟶
      (d.towerPush f).obj ((completedReductionTower U d).obj K) :=
  (d.towerAdjunction f).homEquiv _ _
    ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map
        ((proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f)).counit.app K))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerProjection_natural (K H : d.derived U) (a : K ⟶ H) :
    (completedReductionTower V d).map ((d.push f).map a) ≫ d.towerProjection f H =
      d.towerProjection f K ≫ (d.towerPush f).map
        ((completedReductionTower U d).map a) := by
  let adj := proEtaleRingDerivedAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  unfold AdicCoefficientDatum.towerProjection
  apply (d.towerAdjunction f).homEquiv_naturality_left_square
  have hn := (d.reductionTowerPullbackIso f).hom.naturality_assoc
    ((d.push f).map a) ((completedReductionTower U d).map (adj.counit.app H))
  change (d.towerPull f).map
      ((completedReductionTower V d).map ((d.push f).map a)) ≫
        (d.reductionTowerPullbackIso f).hom.app ((d.push f).obj H) ≫
          (completedReductionTower U d).map (adj.counit.app H) =
    (d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map ((d.pull f).map ((d.push f).map a)) ≫
        (completedReductionTower U d).map (adj.counit.app H) at hn
  rw [Category.assoc, hn]
  simp only [← Functor.map_comp]
  erw [← adj.counit.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduction_eq_stratum :
    d.reductionTowerPullbackIso f = stratumReductionIso d f := by
  apply (completedReductionPullbackIso_existsUnique d f).unique
  · exact (completedReductionPullbackIso_existsUnique d f).choose_spec.1
  · exact (reductionFormula_iff d f _).mpr
      (stratumReductionIso_exists d f).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduction_augmentation (K : d.derived V) :
    (d.towerPull f).map ((completedReductionAugmentation d V).app K) ≫
        (d.reductionTowerPullbackIso f).hom.app K =
      (d.derivedConstantPullbackIso f).hom.app K ≫
        (completedReductionAugmentation d U).app ((d.pull f).obj K) := by
  rw [reduction_eq_stratum]
  exact stratumReduction_augmentation d f K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerProjection_completion (K : d.derived U) :
    d.completionUnit V ((d.push f).obj K) ≫
        (completedRlim V (d.completedRing V)).map (d.towerProjection f K) =
      (d.push f).map (d.completionUnit U K) ≫
        (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) := by
  let a := proEtaleRingDerivedAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  let b := d.towerAdjunction f
  let ax := d.constantRlimAdjunction U
  let ay := d.constantRlimAdjunction V
  let e := TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).hom
  let chi := mateEquiv a b e
  have hm := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.mates_naturality
    a b (completedReductionAugmentation d V) (completedReductionAugmentation d U)
    (d.derivedConstantPullbackIso f).hom (d.reductionTowerPullbackIso f).hom
    (reduction_augmentation d f) K
  have hp : (mateEquiv a b
      (TwoSquare.mk _ _ _ _ (d.reductionTowerPullbackIso f).hom)).app K =
      d.towerProjection f K := by
    simp only [mateEquiv_apply, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
    change _ = b.unit.app _ ≫ (d.towerPush f).map (_ ≫ _)
    simp only [Functor.map_comp]
    repeat first | erw [Category.id_comp] | erw [Category.comp_id]
    rfl
  rw [hp] at hm
  have hu := unit_mateEquiv ax ay chi K
  have hi := iterated_mateEquiv_conjugateEquiv a b ay ax e
  change (mateEquiv ax ay chi) = (d.directImageRlimIso f).hom at hi
  change (d.push f).map (ax.unit.app K) ≫
      (mateEquiv ax ay chi).app ((d.derivedConstantTower U).obj K) =
    ay.unit.app ((d.push f).obj K) ≫
      (completedRlim V (d.completedRing V)).map (chi.app K) at hu
  rw [hi] at hu
  dsimp only [AdicCoefficientDatum.completionUnit]
  rw [Category.assoc, ← Functor.map_comp, hm, Functor.map_comp,
    ← Category.assoc, ← hu]
  simp only [Category.assoc]
  have hn := (d.directImageRlimIso f).hom.naturality
    ((completedReductionAugmentation d U).app K)
  change (d.push f).map ((completedRlim U (d.completedRing U)).map
      ((completedReductionAugmentation d U).app K)) ≫
        (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) =
    (d.directImageRlimIso f).hom.app ((d.derivedConstantTower U).obj K) ≫
      (completedRlim V (d.completedRing V)).map
        ((d.towerPush f).map ((completedReductionAugmentation d U).app K)) at hn
  erw [← hn]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- Evaluate the pushed reduction tower using its canonical K-injective evaluation
comparison, the normalized reduction counit, and the specified scalar-restriction
comparison. Source: blueprint direct image and limits, projection-formula clause
(blueprint: proposition-proper-base-change-complete-integral--1). -/
def AdicCoefficientDatum.towerPushReductionEvaluation
    (K : d.derived U) (n : ℕ) :
    (reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).obj
        ((d.towerPush f).obj ((completedReductionTower U d).obj K)) ⟶
      (reductionDerivedRestrict V (d.projection V n)).obj
        ((d.finitePush f n).obj ((d.reduction U n).obj K)) :=
  (d.towerPushEvaluation f n).hom.app ((completedReductionTower U d).obj K) ≫
    (d.push f).map ((completedReductionEvaluation U d n).app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage f
        (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
        (d.projection V n) (d.projection U n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).inv.app ((d.reduction U n).obj K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerProjection_evaluation (K : d.derived U) (n : ℕ) :
    (reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
        d.towerPushReductionEvaluation f K n =
      (completedReductionEvaluation V d n).app ((d.push f).obj K) ≫
        (reductionDerivedRestrict V (d.projection V n)).map (d.finiteProjection f K n) := by
  let a := proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let EU := reductionTowerDerivedEvaluation U
    (reductionModuleRing U (d.completedRing U)) n
  let EV := reductionTowerDerivedEvaluation V
    (reductionModuleRing V (d.completedRing V)) n
  let RU := (proEtaleRingRestrictScalars (d.projection U n)).mapDerivedCategory
  let RV := (proEtaleRingRestrictScalars (d.projection V n)).mapDerivedCategory
  let u : completedReductionTower U d ⋙ EU ⟶
      d.reduction U n ⋙ RU :=
    completedReductionEvaluation U d n
  let v : completedReductionTower V d ⋙ EV ⟶
      d.reduction V n ⋙ RV :=
    completedReductionEvaluation V d n
  let δ := proEtaleRingRestrictionDerivedDirectImage f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let r := proEtaleRingRestrictionDerivedPullback f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let t := (d.chi f n).hom.app ((d.push f).obj K) ≫
    (d.reduction U n).map (a.counit.app K)
  have ht : (stratumTowerEvaluationIso d f n).inv.app
        ((completedReductionTower V d).obj ((d.push f).obj K)) ≫
      EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
        (completedReductionTower U d).map (a.counit.app K)) ≫ u.app K =
    (d.pull f).map (v.app ((d.push f).obj K)) ≫
      r.inv.app ((d.reduction V n).obj ((d.push f).obj K)) ≫
        (RU).map t := by
    have he := stratumReduction_evaluation d f n ((d.push f).obj K)
    rw [← reduction_eq_stratum] at he
    change EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K)) ≫
        u.app ((d.pull f).obj ((d.push f).obj K)) =
      (stratumTowerEvaluationIso d f n).hom.app
          ((completedReductionTower V d).obj ((d.push f).obj K)) ≫
        (d.pull f).map (v.app ((d.push f).obj K)) ≫
          r.inv.app ((d.reduction V n).obj ((d.push f).obj K)) ≫
            (RU).map
              ((d.chi f n).hom.app ((d.push f).obj K)) at he
    have hn := u.naturality (a.counit.app K)
    change EU.map ((completedReductionTower U d).map (a.counit.app K)) ≫ u.app K =
      u.app ((d.pull f).obj ((d.push f).obj K)) ≫
        RU.map ((d.reduction U n).map (a.counit.app K)) at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    rw [← Category.assoc
      (EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K)))
      (u.app ((d.pull f).obj ((d.push f).obj K)))
      (RU.map ((d.reduction U n).map (a.counit.app K))), he]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← RU.map_comp]
    rfl
  have hm := _root_.mate_adjunct (d.towerAdjunction f) a
    (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)
    ((completedReductionTower V d).obj ((d.push f).obj K))
    ((completedReductionTower U d).obj K)
    ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map (a.counit.app K))
  change a.homEquiv _ _
    ((stratumTowerEvaluationIso d f n).inv.app
        ((completedReductionTower V d).obj ((d.push f).obj K)) ≫
      EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
        (completedReductionTower U d).map (a.counit.app K))) =
    EV.map (d.towerProjection f K) ≫
      (mateEquiv (d.towerAdjunction f) a
        (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)).app _ at hm
  rw [← towerPushEvaluation_mate] at hm
  apply (cancel_mono (δ.hom.app ((d.reduction U n).obj K))).mp
  dsimp only [AdicCoefficientDatum.towerPushReductionEvaluation]
  change (EV.map (d.towerProjection f K) ≫
      ((d.towerPushEvaluation f n).hom.app ((completedReductionTower U d).obj K) ≫
        (d.push f).map (u.app K) ≫ δ.inv.app ((d.reduction U n).obj K))) ≫
      δ.hom.app ((d.reduction U n).obj K) =
    (v.app ((d.push f).obj K) ≫ RV.map (d.finiteProjection f K n)) ≫
      δ.hom.app ((d.reduction U n).obj K)
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [← Category.assoc, ← hm]
  erw [← a.homEquiv_naturality_right]
  rw [Category.assoc, ht]
  erw [a.homEquiv_naturality_left]
  have hs := (proEtaleRingSheafChangeAdjunction f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)).2.2
      ((d.reduction V n).obj ((d.push f).obj K)) ((d.reduction U n).obj K) t
  erw [hs]
  rfl

/-- The specified tower projection evaluates to the finite projection formula, is
natural in arbitrary morphisms, and identifies the two completion units. The map
is one morphism of derived strict towers, retaining every quotient transition.
Source: blueprint direct image and limits, projection and completeness clauses;
Stacks Tags 0944 and 099N (blueprint: proposition-proper-base-change-complete-integral--1).
Proof: on flat-term K-flat models the scalar/pullback mate is tensor balancing.
Transposition of its composite with the counit is exactly finiteProjection, by the
normalized scalar-change adjunction comparison. The same tensor maps commute with
quotient transitions and chain maps, giving the strict tower map and naturality.
The constant-to-reduction augmentation has the same quotient-unit formula. Apply
adjunction transposition and the constant/pullback comparison: the resulting
completion map is direct image of the original unit followed by directImageRlimIso.
This is the last displayed equality. Perfectness makes the tower projection
invertible, by conservativity of evaluation for isomorphisms. -/
theorem AdicCoefficientDatum.towerProjection_properties (K : d.derived U) :
    (∀ n : ℕ,
      (reductionTowerDerivedEvaluation V
          (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
          d.towerPushReductionEvaluation f K n =
        (completedReductionEvaluation V d n).app ((d.push f).obj K) ≫
          (reductionDerivedRestrict V (d.projection V n)).map (d.finiteProjection f K n)) ∧
      (∀ (H : d.derived U) (a : K ⟶ H),
        (completedReductionTower V d).map ((d.push f).map a) ≫ d.towerProjection f H =
          d.towerProjection f K ≫
            (d.towerPush f).map ((completedReductionTower U d).map a)) ∧
      d.completionUnit V ((d.push f).obj K) ≫
          (completedRlim V (d.completedRing V)).map (d.towerProjection f K) =
        (d.push f).map (d.completionUnit U K) ≫
          (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) := by
  exact ⟨towerProjection_evaluation d f K, towerProjection_natural d f K,
    towerProjection_completion d f K⟩

private theorem derivedTowerIsIso
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    {X Y : DerivedCategory (ℕᵒᵖ ⥤ B)} (a : X ⟶ Y)
    (h : ∀ n : ℕᵒᵖ,
      IsIso ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory).map a)) :
    IsIso a := by
  rw [DerivedCategory.isIso_iff]
  intro i
  have (n : ℕᵒᵖ) : IsIso
      (((DerivedCategory.homologyFunctor (ℕᵒᵖ ⥤ B) i).map a).app n) := by
    let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
    have : IsIso ((E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B i).map a) := by
      change IsIso ((DerivedCategory.homologyFunctor B i).map (E.mapDerivedCategory.map a))
      let := h n
      infer_instance
    exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i) a).2 inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- Perfect quotient coefficients make the specified strict projection invertible.
Source: blueprint tower compatibility; Stacks Tags 0944 and 015F
(blueprint: proposition-proper-base-change-complete-integral--1).
Proof: evaluate the tower adjunction mate. The coefficient restriction/pullback
comparisons identify its evaluation with the restriction of the finite projection.
The latter is invertible by the perfect projection formula. The cone of the tower map
therefore has zero cohomology at every index. Tower cohomology is levelwise, hence its
cone is acyclic and the original strict derived tower map is invertible. This uses
conservativity for isomorphisms, without claiming faithfulness of derived evaluations. -/
theorem AdicCoefficientDatum.towerProjection_isIso {U V : Scheme.{t}} (f : U ⟶ V)
    (K : d.derived U) : IsIso (d.towerProjection f K) := by
  have he (n : ℕ) : IsIso
      ((reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K)) := by
    have h := (d.towerProjection_properties f K).1 n
    have : IsIso ((reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
        d.towerPushReductionEvaluation f K n) := by
      rw [h]
      infer_instance
    have : IsIso (d.towerPushReductionEvaluation f K n) := by
      unfold AdicCoefficientDatum.towerPushReductionEvaluation
      infer_instance
    exact IsIso.of_isIso_comp_right _ (d.towerPushReductionEvaluation f K n)
  exact derivedTowerIsIso (B := ringedSiteModules.{t + 1}
    (reductionModuleRing V (d.completedRing V))) (d.towerProjection f K)
    (fun n ↦ he n.unop)

attribute [instance] AdicCoefficientDatum.towerProjection_isIso

/-- Direct image preserves quotient-tower completeness, with the specified completion unit.
Source: blueprint direct image and limits; Stacks Tag 099N (3), (4)
(blueprint: proposition-proper-base-change-complete-integral--1).
Proof: the perfect projection-formula maps identify the strict reduction tower of Rf_*K
with derived tower pushforward of K's strict reduction tower. Their quotient compatibility
is the tensor-unit normalization. The canonical completion unit of Rf_*K
then equals Rf_* of K's completion unit followed by the canonical direct-image/Rlim
comparison. Both maps are invertible, the first by hK and the second by its construction
as a conjugate of the constant/pullback identity square. Thus the completion unit is
invertible, which is exactly quotient-tower completeness at V.
No faithfulness of derived evaluations is invoked. -/
theorem AdicCoefficientDatum.push_complete (K : d.derived U)
    (hK : d.TowerComplete U K) : d.TowerComplete V ((d.push f).obj K) := by
  let : IsIso (d.completionUnit U K) := hK
  change IsIso (d.completionUnit V ((d.push f).obj K))
  have h := (d.towerProjection_properties f K).2.2
  have : IsIso (d.completionUnit V ((d.push f).obj K) ≫
      (completedRlim V (d.completedRing V)).map (d.towerProjection f K)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((completedRlim V (d.completedRing V)).map (d.towerProjection f K))

end AlgebraicGeometry.Scheme
