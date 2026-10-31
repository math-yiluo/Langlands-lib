import Langlands.Cohomology.ExactDerivedEvaluation
import Langlands.Shimura.Coefficients.HarrisEtaleDerivedSourceChange

/-! # Evaluating actual Harris derived source changes -/

noncomputable section

universe u wC wK wL wM wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.Global
open Langlands.Sheaf Langlands.Cohomology

private theorem squareSingleRecovery
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K : Type*} [Category* K] [Abelian K] [HasDerivedCategory K]
    {L : Type*} [Category* L] [Abelian L] [HasDerivedCategory L]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : C ⥤ L) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : C ⥤ K) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : L ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (P : K ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (e : F ⋙ T ≅ G ⋙ P) (M : C) (q : ℤ) :
    (exactDerivedEvaluationSingleIso T q ((F.mapDerivedCategorySingleFunctor q).app M)).inv ≫
        (exactDerivedSquareIso F G T P e).hom.app
          ((DerivedCategory.singleFunctor C q).obj M) ≫
        (exactDerivedEvaluationSingleIso P q ((G.mapDerivedCategorySingleFunctor q).app M)).hom =
      (DerivedCategory.singleFunctor B q).map (e.hom.app M) := by
  rw [exactDerivedSquareIso_hom_app_single]
  simp only [exactDerivedEvaluationSingleIso, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n)) (k l : ℕᵒᵖ)

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

variable [HasDerivedCategory.{wM}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]
variable [HasDerivedCategory.{wT}
  (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]

/-- Evaluate the mixed diagram, whose outgoing indices start at l while its
sheaves live on the source slice over Y k, on actual derived categories. -/
def harrisEtaleDerivedMixedEvaluation (i : Under l) :
    DerivedCategory (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) ⥤
      DerivedCategory (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) :=
  ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i).mapDerivedCategory

instance (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).CommShift ℤ := by
  dsimp [harrisEtaleDerivedMixedEvaluation]
  infer_instance

instance (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).IsTriangulated := by
  dsimp [harrisEtaleDerivedMixedEvaluation]
  infer_instance

variable [HasDerivedCategory.{wC} (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
  (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]
variable [HasDerivedCategory.{wK}
  (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]
variable [HasDerivedCategory.{wL}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj l))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]

/-- The restricted coefficient endpoint evaluated at a reachable exponent,
compared with the same ordinary sheaf placed in the original cochain degree. -/
def harrisEtaleDerivedRestrictedCoefficientEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceRestrictionDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY l q)) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        (((sourceSliceRestriction X.smallEtaleTopology
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).obj
          (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY l)).obj i) :=
  exactDerivedEvaluationSingleIso
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedRestrictedCoefficientSingleIso ρ p U m X Y hY f q)

def harrisEtaleDerivedRestrictedConstantEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceRestrictionDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalConstant ρ p U m X Y l q)) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        (((sourceSliceRestriction X.smallEtaleTopology
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).obj
          (harrisEtaleLocalConstantSystem ρ p U m X Y l)).obj i) :=
  exactDerivedEvaluationSingleIso
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedRestrictedConstantSingleIso ρ p U m X Y f q)

/-- The reindexed coefficient endpoint evaluates at the composite outgoing
arrow f followed by i.hom. -/
def harrisEtaleDerivedReindexedCoefficientEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceReindexDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q)) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        ((harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k).obj
          ((Under.map f).obj i)) :=
  exactDerivedEvaluationSingleIso
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedReindexedCoefficientSingleIso ρ p U m X Y hY f q)

def harrisEtaleDerivedReindexedConstantEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceReindexDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalConstant ρ p U m X Y k q)) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        ((harrisEtaleLocalConstantSystem ρ p U m X Y k).obj
          ((Under.map f).obj i)) :=
  exactDerivedEvaluationSingleIso
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedReindexedConstantSingleIso ρ p U m X Y f q)

/-- Evaluate the constructed associated source change on the actual derived
category of sheaves over the source cover. -/
def harrisEtaleDerivedCoefficientSourceChangeEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceRestrictionDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY l q)) ≅
      (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceReindexDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q)) :=
  (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).mapIso
    (harrisEtaleDerivedLocalCoefficientSourceChangeIso ρ p U m X Y hY f q)

def harrisEtaleDerivedConstantSourceChangeEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceRestrictionDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalConstant ρ p U m X Y l q)) ≅
      (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceReindexDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalConstant ρ p U m X Y k q)) :=
  (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).mapIso
    (harrisEtaleDerivedLocalConstantSourceChangeIso ρ p U m X Y f q)

/-- Invariant evaluation after actual source restriction, evaluated in the
mixed derived category of sheaves over Y k. -/
def harrisEtaleDerivedRestrictedTrivializationEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceRestrictionDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY l q)) ≅
      (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceRestrictionDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalConstant ρ p U m X Y l q)) :=
  (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).mapIso
    ((etaleSourceRestrictionDerivedFunctor X Y f).mapIso
      (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY l q))

/-- Invariant evaluation after actual outgoing-arrow reindexing, evaluated
in the same mixed derived category. -/
def harrisEtaleDerivedReindexedTrivializationEvaluationIso
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceReindexDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q)) ≅
      (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).obj
        ((etaleSourceReindexDerivedFunctor X Y f).obj
          (harrisEtaleDerivedLocalConstant ρ p U m X Y k q)) :=
  (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).mapIso
    ((etaleSourceReindexDerivedFunctor X Y f).mapIso
      (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q))

set_option maxHeartbeats 1600000 in
/-- Through the constructed endpoint comparisons, evaluated coefficient
source change recovers the original ordinary component in degree q. -/
@[reassoc] theorem harrisEtaleDerivedCoefficientSourceChangeEvaluationIso_single
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedRestrictedCoefficientEvaluationIso ρ p U m X Y hY k l f q i).inv ≫
        (harrisEtaleDerivedCoefficientSourceChangeEvaluationIso ρ p U m X Y hY k l f q i).hom ≫
        (harrisEtaleDerivedReindexedCoefficientEvaluationIso ρ p U m X Y hY k l f q i).hom =
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
        ((harrisEtaleLocalCoefficientSourceChangeIso ρ p U m X Y hY f).hom.app i) := by
  exact exactDerivedEvaluation_single
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedRestrictedCoefficientSingleIso ρ p U m X Y hY f q)
    (harrisEtaleDerivedReindexedCoefficientSingleIso ρ p U m X Y hY f q)
    (harrisEtaleDerivedLocalCoefficientSourceChangeIso ρ p U m X Y hY f q).hom
    (harrisEtaleLocalCoefficientSourceChangeIso ρ p U m X Y hY f).hom
    (squareSingleRecovery (etaleAssociatedSourceSystemFunctor X Y hY l) (etaleAssociatedSourceSystemFunctor X Y hY k)
      (sourceSliceRestriction X.smallEtaleTopology
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f)
      (sourceSliceReindex X.smallEtaleTopology
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f)
      (etaleAssociatedSourceChangeFunctorIso X Y hY f) (harrisCoefficientDiagram ρ p U m) q)

set_option maxHeartbeats 1600000 in
/-- Through the constructed endpoint comparisons, evaluated constant
source change recovers the original ordinary component in degree q. -/
@[reassoc] theorem harrisEtaleDerivedConstantSourceChangeEvaluationIso_single
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedRestrictedConstantEvaluationIso ρ p U m X Y k l f q i).inv ≫
        (harrisEtaleDerivedConstantSourceChangeEvaluationIso ρ p U m X Y k l f q i).hom ≫
        (harrisEtaleDerivedReindexedConstantEvaluationIso ρ p U m X Y k l f q i).hom =
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
        ((harrisEtaleLocalConstantSourceChangeIso ρ p U m X Y f).hom.app i) := by
  exact exactDerivedEvaluation_single
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedRestrictedConstantSingleIso ρ p U m X Y f q)
    (harrisEtaleDerivedReindexedConstantSingleIso ρ p U m X Y f q)
    (harrisEtaleDerivedLocalConstantSourceChangeIso ρ p U m X Y f q).hom
    (harrisEtaleLocalConstantSourceChangeIso ρ p U m X Y f).hom
    (squareSingleRecovery (etaleConstantSourceSystemFunctor X Y l) (etaleConstantSourceSystemFunctor X Y k)
      (sourceSliceRestriction X.smallEtaleTopology
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f)
      (sourceSliceReindex X.smallEtaleTopology
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f)
      (etaleConstantSourceChangeFunctorIso X Y f) (harrisCoefficientDiagram ρ p U m) q)

omit [HasDerivedCategory.{wK}
  (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))] in
set_option maxHeartbeats 1600000 in
/-- Evaluated restriction recovers pullback of the original invariant
section evaluation along the outgoing arrow from l. -/
@[reassoc] theorem harrisEtaleDerivedRestrictedTrivializationEvaluationIso_single
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedRestrictedCoefficientEvaluationIso ρ p U m X Y hY k l f q i).inv ≫
        (harrisEtaleDerivedRestrictedTrivializationEvaluationIso ρ p U m X Y hY k l f q i).hom ≫
        (harrisEtaleDerivedRestrictedConstantEvaluationIso ρ p U m X Y k l f q i).hom =
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
        ((X.smallEtaleTopology.overMapPullback
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) (Y.obj.map f)).map
            (etaleAssociatedEvaluationAlong X Y (harrisCoefficientDiagram ρ p U m)
              i.right (Y.obj.map i.hom))) := by
  exact exactDerivedEvaluation_single
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedRestrictedCoefficientSingleIso ρ p U m X Y hY f q)
    (harrisEtaleDerivedRestrictedConstantSingleIso ρ p U m X Y f q)
    ((etaleSourceRestrictionDerivedFunctor X Y f).map
      (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY l q).hom)
    ((sourceSliceRestriction X.smallEtaleTopology
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).map
        (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY l).hom)
    (exactDerivedEvaluation_single
      (sourceSliceRestriction X.smallEtaleTopology
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f) q
      (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY l q)
      (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y l q)
      (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY l q).hom
      (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY l).hom
      (harrisEtaleDerivedLocalCoefficientIso_single ρ p U m X Y hY l q))

omit [HasDerivedCategory.{wL}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj l))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))] in
set_option maxHeartbeats 1600000 in
/-- Evaluated reindexing recovers original invariant-section evaluation
along the genuine composite cover map f followed by i.hom. -/
@[reassoc] theorem harrisEtaleDerivedReindexedTrivializationEvaluationIso_single
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedReindexedCoefficientEvaluationIso ρ p U m X Y hY k l f q i).inv ≫
        (harrisEtaleDerivedReindexedTrivializationEvaluationIso ρ p U m X Y hY k l f q i).hom ≫
        (harrisEtaleDerivedReindexedConstantEvaluationIso ρ p U m X Y k l f q i).hom =
      (DerivedCategory.singleFunctor
        (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
          (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
        (etaleAssociatedEvaluationAlong X Y (harrisCoefficientDiagram ρ p U m)
          i.right (Y.obj.map (f ≫ i.hom))) := by
  exact exactDerivedEvaluation_single
    ((CategoryTheory.evaluation (Under l) (Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)))).obj i) q
    (harrisEtaleDerivedReindexedCoefficientSingleIso ρ p U m X Y hY f q)
    (harrisEtaleDerivedReindexedConstantSingleIso ρ p U m X Y f q)
    ((etaleSourceReindexDerivedFunctor X Y f).map
      (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q).hom)
    ((sourceSliceReindex X.smallEtaleTopology
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).map
        (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom)
    (exactDerivedEvaluation_single
      (sourceSliceReindex X.smallEtaleTopology
        (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f) q
      (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY k q)
      (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y k q)
      (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q).hom
      (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom
      (harrisEtaleDerivedLocalCoefficientIso_single ρ p U m X Y hY k q))

/-- The evaluated actual derived source-change square commutes for the
original full Harris coefficient diagram. -/
@[reassoc] theorem harrisEtaleDerivedTrivializationEvaluationIso_sourceChange
    (f : k ⟶ l) (q : ℤ) (i : Under l) :
    (harrisEtaleDerivedRestrictedTrivializationEvaluationIso ρ p U m X Y hY k l f q i).hom ≫
        (harrisEtaleDerivedConstantSourceChangeEvaluationIso ρ p U m X Y k l f q i).hom =
      (harrisEtaleDerivedCoefficientSourceChangeEvaluationIso ρ p U m X Y hY k l f q i).hom ≫
        (harrisEtaleDerivedReindexedTrivializationEvaluationIso ρ p U m X Y hY k l f q i).hom := by
  change (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).map _ ≫
      (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).map _ =
    (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).map _ ≫
      (harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((harrisEtaleDerivedMixedEvaluation ρ p U m X Y k l i).map)
    (harrisEtaleDerivedLocalCoefficientIso_sourceChange ρ p U m X Y hY f q)

end Langlands.Shimura.Coefficients
