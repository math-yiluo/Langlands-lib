import Langlands.Shimura.Coefficients.HarrisEtaleDerivedLocalTrivialization
import Langlands.Shimura.Coefficients.VaryingCoverDerivedSourceChange

/-! # Source changes for the actual Harris derived coefficient objects -/

noncomputable section

universe u wC wK wL wM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Langlands.Global Langlands.Sheaf

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n)) {k l : ℕᵒᵖ}

attribute [local instance] etaleAssociatedSourceSystemFunctorPreservesFiniteLimits
  etaleAssociatedSourceSystemFunctorPreservesFiniteColimits

/-- The ordinary full Harris coefficient diagram changes source by the actual
map of torsors and the outgoing-arrow reindexing. -/
def harrisEtaleLocalCoefficientSourceChangeIso (f : k ⟶ l) :
    (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p))
        Y.obj f).obj (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY l) ≅
      (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p))
        Y.obj f).obj (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k) :=
  (etaleAssociatedSourceChangeFunctorIso X Y hY f).app (harrisCoefficientDiagram ρ p U m)

/-- Source change for the original whole-lattice reductions made constant. -/
def harrisEtaleLocalConstantSourceChangeIso (f : k ⟶ l) :
    (sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p))
        Y.obj f).obj (harrisEtaleLocalConstantSystem ρ p U m X Y l) ≅
      (sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p))
        Y.obj f).obj (harrisEtaleLocalConstantSystem ρ p U m X Y k) :=
  (etaleConstantSourceChangeFunctorIso X Y f).app (harrisCoefficientDiagram ρ p U m)

/-- On every common sheaf section the ordinary associated comparison is the
identity, despite the different slice and index descriptions. -/
@[simp] theorem harrisEtaleLocalCoefficientSourceChangeIso_hom_app_hom_app
    (f : k ⟶ l) (i : Under l) (V : (Over (Y.obj.obj k))ᵒᵖ) :
    ((harrisEtaleLocalCoefficientSourceChangeIso ρ p U m X Y hY f).hom.app i).hom.app V =
      𝟙 _ := rfl

@[simp] theorem harrisEtaleLocalConstantSourceChangeIso_hom_app_hom_app
    (f : k ⟶ l) (i : Under l) (V : (Over (Y.obj.obj k))ᵒᵖ) :
    ((harrisEtaleLocalConstantSourceChangeIso ρ p U m X Y f).hom.app i).hom.app V =
      𝟙 _ := rfl

/-- At each reachable exponent, source change carries the original invariant
evaluation to evaluation at the composite genuine cover map. -/
@[reassoc] theorem harrisEtaleLocalCoefficientSourceChange_evaluation
    (f : k ⟶ l) (i : Under l) :
    (X.smallEtaleTopology.overMapPullback (ModuleCat.{u} (HarrisCoefficientIntegers L p))
        (Y.obj.map f)).map
        ((harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY l).hom.app i) ≫
      (harrisEtaleLocalConstantSourceChangeIso ρ p U m X Y f).hom.app i =
    (harrisEtaleLocalCoefficientSourceChangeIso ρ p U m X Y hY f).hom.app i ≫
      (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app
        ((Under.map f).obj i) :=
  congr_app (etaleAssociatedSourceTrivialization_sourceChange X Y hY f
    (harrisCoefficientDiagram ρ p U m)) i

/-- Reindexing evaluates along the genuine composite cover map. -/
@[simp] theorem harrisEtaleLocalCoefficientDiagramIso_reindex_hom_app
    (f : k ⟶ l) (i : Under l) :
    (harrisEtaleLocalCoefficientDiagramIso ρ p U m X Y hY k).hom.app
        ((Under.map f).obj i) =
      etaleAssociatedEvaluationAlong X Y (harrisCoefficientDiagram ρ p U m)
        i.right (Y.obj.map (f ≫ i.hom)) := rfl

variable [HasDerivedCategory.{wC} (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
  (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]
variable [HasDerivedCategory.{wK}
  (Under k ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]
variable [HasDerivedCategory.{wL}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj l))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]
variable [HasDerivedCategory.{wM}
  (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
    (ModuleCat.{u} (HarrisCoefficientIntegers L p)))]

/-- Actual derived source change of the whole Harris coefficient diagram in
any integer cochain degree. -/
def harrisEtaleDerivedLocalCoefficientSourceChangeIso (f : k ⟶ l) (q : ℤ) :
    (etaleSourceRestrictionDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY l q) ≅
      (etaleSourceReindexDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q) :=
  (etaleAssociatedSourceDerivedChangeIso X Y hY f).app
    ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
      (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m))

def harrisEtaleDerivedLocalConstantSourceChangeIso (f : k ⟶ l) (q : ℤ) :
    (etaleSourceRestrictionDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalConstant ρ p U m X Y l q) ≅
      (etaleSourceReindexDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalConstant ρ p U m X Y k q) :=
  (etaleConstantSourceDerivedChangeIso X Y f).app
    ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
      (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m))

/-- Compare derived restriction of the Harris coefficient object with the
ordinary restricted diagram in the same single degree. -/
def harrisEtaleDerivedRestrictedCoefficientSingleIso (f : k ⟶ l) (q : ℤ) :
    (etaleSourceRestrictionDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY l q) ≅
      (DerivedCategory.singleFunctor (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        ((sourceSliceRestriction X.smallEtaleTopology
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).obj
          (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY l)) :=
  (etaleSourceRestrictionDerivedFunctor X Y f).mapIso
      (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY l q) ≪≫
    ((sourceSliceRestriction X.smallEtaleTopology
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).app
      ((etaleAssociatedSourceSystemFunctor X Y hY l).obj (harrisCoefficientDiagram ρ p U m))

def harrisEtaleDerivedRestrictedConstantSingleIso (f : k ⟶ l) (q : ℤ) :
    (etaleSourceRestrictionDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalConstant ρ p U m X Y l q) ≅
      (DerivedCategory.singleFunctor (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        ((sourceSliceRestriction X.smallEtaleTopology
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).obj
          (harrisEtaleLocalConstantSystem ρ p U m X Y l)) :=
  (etaleSourceRestrictionDerivedFunctor X Y f).mapIso
      (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y l q) ≪≫
    ((sourceSliceRestriction X.smallEtaleTopology
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).app
      ((etaleConstantSourceSystemFunctor X Y l).obj (harrisCoefficientDiagram ρ p U m))

/-- The corresponding comparison for reindexing by Under.map f. -/
def harrisEtaleDerivedReindexedCoefficientSingleIso (f : k ⟶ l) (q : ℤ) :
    (etaleSourceReindexDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalCoefficient ρ p U m X Y hY k q) ≅
      (DerivedCategory.singleFunctor (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        ((sourceSliceReindex X.smallEtaleTopology
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).obj
          (harrisEtaleLocalCoefficientSystem ρ p U m X Y hY k)) :=
  (etaleSourceReindexDerivedFunctor X Y f).mapIso
      (harrisEtaleDerivedLocalCoefficientSingleIso ρ p U m X Y hY k q) ≪≫
    ((sourceSliceReindex X.smallEtaleTopology
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).app
      ((etaleAssociatedSourceSystemFunctor X Y hY k).obj (harrisCoefficientDiagram ρ p U m))

def harrisEtaleDerivedReindexedConstantSingleIso (f : k ⟶ l) (q : ℤ) :
    (etaleSourceReindexDerivedFunctor X Y f).obj
        (harrisEtaleDerivedLocalConstant ρ p U m X Y k q) ≅
      (DerivedCategory.singleFunctor (Under l ⥤ Sheaf (X.smallEtaleTopology.over (Y.obj.obj k))
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
        ((sourceSliceReindex X.smallEtaleTopology
          (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).obj
          (harrisEtaleLocalConstantSystem ρ p U m X Y k)) :=
  (etaleSourceReindexDerivedFunctor X Y f).mapIso
      (harrisEtaleDerivedLocalConstantSingleIso ρ p U m X Y k q) ≪≫
    ((sourceSliceReindex X.smallEtaleTopology
      (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).app
      ((etaleConstantSourceSystemFunctor X Y k).obj (harrisCoefficientDiagram ρ p U m))

set_option maxHeartbeats 1600000 in
/-- Single-degree recovery for the complete Harris diagram, with all
canonical restriction, ordinary source-change and reindexing factors. -/
@[reassoc] theorem harrisEtaleDerivedLocalCoefficientSourceChangeIso_single
    (f : k ⟶ l) (q : ℤ) :
    (etaleAssociatedSourceDerivedChangeIso X Y hY f).hom.app
        ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m) (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m)) =
      (etaleSourceRestrictionDerivedFunctor X Y f).map
          (((etaleAssociatedSourceSystemFunctor X Y hY l).mapDerivedCategorySingleFunctor q).hom.app (harrisCoefficientDiagram ρ p U m)) ≫
        ((sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).hom.app
          ((etaleAssociatedSourceSystemFunctor X Y hY l).obj (harrisCoefficientDiagram ρ p U m)) ≫
        (DerivedCategory.singleFunctor (Under l ⥤ Sheaf ((X.smallEtaleTopology).over (Y.obj.obj k)) (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
          ((etaleAssociatedSourceChangeFunctorIso X Y hY f).hom.app (harrisCoefficientDiagram ρ p U m)) ≫
        ((sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).inv.app
          ((etaleAssociatedSourceSystemFunctor X Y hY k).obj (harrisCoefficientDiagram ρ p U m)) ≫
        (etaleSourceReindexDerivedFunctor X Y f).map
          (((etaleAssociatedSourceSystemFunctor X Y hY k).mapDerivedCategorySingleFunctor q).inv.app (harrisCoefficientDiagram ρ p U m)) :=
  etaleAssociatedSourceDerivedChangeIso_hom_app_single X Y hY f
    (harrisCoefficientDiagram ρ p U m) q

set_option maxHeartbeats 1600000 in
@[reassoc] theorem harrisEtaleDerivedLocalConstantSourceChangeIso_single
    (f : k ⟶ l) (q : ℤ) :
    (etaleConstantSourceDerivedChangeIso X Y f).hom.app
        ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m) (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m)) =
      (etaleSourceRestrictionDerivedFunctor X Y f).map
          (((etaleConstantSourceSystemFunctor X Y l).mapDerivedCategorySingleFunctor q).hom.app (harrisCoefficientDiagram ρ p U m)) ≫
        ((sourceSliceRestriction X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).hom.app
          ((etaleConstantSourceSystemFunctor X Y l).obj (harrisCoefficientDiagram ρ p U m)) ≫
        (DerivedCategory.singleFunctor (Under l ⥤ Sheaf ((X.smallEtaleTopology).over (Y.obj.obj k)) (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).map
          ((etaleConstantSourceChangeFunctorIso X Y f).hom.app (harrisCoefficientDiagram ρ p U m)) ≫
        ((sourceSliceReindex X.smallEtaleTopology (ModuleCat.{u} (HarrisCoefficientIntegers L p)) Y.obj f).mapDerivedCategorySingleFunctor q).inv.app
          ((etaleConstantSourceSystemFunctor X Y k).obj (harrisCoefficientDiagram ρ p U m)) ≫
        (etaleSourceReindexDerivedFunctor X Y f).map
          (((etaleConstantSourceSystemFunctor X Y k).mapDerivedCategorySingleFunctor q).inv.app (harrisCoefficientDiagram ρ p U m)) :=
  etaleConstantSourceDerivedChangeIso_hom_app_single X Y f
    (harrisCoefficientDiagram ρ p U m) q

/-- Actual derived invariant evaluation commutes with changing the source
torsor for the whole Harris lattice diagram in every integer cochain degree. -/
@[reassoc] theorem harrisEtaleDerivedLocalCoefficientIso_sourceChange
    (f : k ⟶ l) (q : ℤ) :
    (etaleSourceRestrictionDerivedFunctor X Y f).map
        (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY l q).hom ≫
      (etaleConstantSourceDerivedChangeIso X Y f).hom.app
      ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
        (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj
          (harrisCoefficientDiagram ρ p U m)) =
    (harrisEtaleDerivedLocalCoefficientSourceChangeIso ρ p U m X Y hY f q).hom ≫
      (etaleSourceReindexDerivedFunctor X Y f).map
        (harrisEtaleDerivedLocalCoefficientIso ρ p U m X Y hY k q).hom :=
  etaleAssociatedSourceDerivedTrivialization_sourceChange_app X Y hY f
    ((DerivedCategory.singleFunctor (EquivariantDiagram (harrisCongruenceGroups ρ p U m)
      (ModuleCat.{u} (HarrisCoefficientIntegers L p))) q).obj (harrisCoefficientDiagram ρ p U m))

end Langlands.Shimura.Coefficients
