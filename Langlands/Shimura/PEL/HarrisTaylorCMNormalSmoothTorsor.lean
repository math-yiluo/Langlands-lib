import Langlands.Shimura.PEL.HarrisTaylorCMNormalSmoothEtale
import Langlands.Shimura.PEL.HarrisTaylorCMNormalTorsor
import Langlands.Shimura.PEL.HarrisTaylorCMKernelSchemeIsomorphism

/-! # Original CM geometric torsors from the dominant criterion -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The existing finite-geometric-torsor interface for the original action,
with original etaleness and kernel comparison invertibility both derived. -/
def representedCMNormalGeometricTorsor_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    {Y : Action ((schemes R).obj U).Etale (SmallCMResidualGroup D U V) //
      Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U) Y} := by
  have : Etale (projection R U V hVU) :=
    representedCMNormalProjection_etale_of_dominantCriterion D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid criterion
  have : IsIso (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_isIso_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  exact representedCMNormalGeometricTorsor D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry

local notation "derivedTorsor" => representedCMNormalGeometricTorsor_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor

/-- The same original residual action in the actual finite-etale cover category. -/
def representedCMNormalFiniteEtaleAction_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Action (Cover ((schemes R).obj U)) (SmallCMResidualGroup D U V) := by
  have : Etale (projection R U V hVU) :=
    representedCMNormalProjection_etale_of_dominantCriterion D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid criterion
  exact representedCMNormalFiniteEtaleAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU

local notation "derivedFiniteAction" => representedCMNormalFiniteEtaleAction_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor

section Identifications

@[simp] theorem representedCMNormalGeometricTorsor_of_dominantCriterion_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (derivedTorsor R U V hVU existence geometry hRigid criterion).val.V.left =
      (schemes R).obj V := rfl

@[simp] theorem representedCMNormalGeometricTorsor_of_dominantCriterion_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (derivedTorsor R U V hVU existence geometry hRigid criterion).val.V.hom =
      projection R U V hVU := rfl

@[simp] theorem representedCMNormalGeometricTorsor_of_dominantCriterion_ρ_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0})
    (g : SmallCMResidualGroup D U V) :
    ((derivedTorsor R U V hVU existence geometry hRigid criterion).val.ρ g).left =
      (quotientAction R U V hVU).ρ g := rfl

@[simp] theorem representedCMNormalFiniteEtaleAction_of_dominantCriterion_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (derivedFiniteAction R U V hVU existence geometry hRigid criterion).V.obj.left =
      (schemes R).obj V := rfl

@[simp] theorem representedCMNormalFiniteEtaleAction_of_dominantCriterion_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (derivedFiniteAction R U V hVU existence geometry hRigid criterion).V.obj.hom =
      projection R U V hVU := rfl

@[simp] theorem representedCMNormalFiniteEtaleAction_of_dominantCriterion_ρ_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0})
    (g : SmallCMResidualGroup D U V) :
    ((derivedFiniteAction R U V hVU existence geometry hRigid criterion).ρ g).hom.left =
      (quotientAction R U V hVU).ρ g := rfl

end Identifications

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenQuotientAction" => cmNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The original finite geometric torsor for exactly the witnesses defining
`cmSchemeTower q`, with no original etaleness or IsIso premise. -/
def cmNormalGeometricTorsor_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    {Y : Action ((chosenSchemes q).obj U).Etale (SmallCMResidualGroup D U V) //
      Coefficients.IsFiniteGeometricTorsor ((chosenSchemes q).obj U) Y} :=
  derivedTorsor (chosenReps q) U V hVU existence geometry hRigid criterion

/-- The identical chosen residual action in finite-etale covers of its
original coarse level. -/
def cmNormalFiniteEtaleAction_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Action (Cover ((chosenSchemes q).obj U)) (SmallCMResidualGroup D U V) :=
  derivedFiniteAction (chosenReps q) U V hVU existence geometry hRigid criterion

local notation "chosenDerivedTorsor" => cmNormalGeometricTorsor_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor U V hVU q
local notation "chosenDerivedFiniteAction" => cmNormalFiniteEtaleAction_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor U V hVU q

section ChosenIdentifications

@[simp] theorem cmNormalGeometricTorsor_of_dominantCriterion_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (chosenDerivedTorsor existence geometry hRigid criterion).val.V.left =
      (chosenSchemes q).obj V := rfl

@[simp] theorem cmNormalGeometricTorsor_of_dominantCriterion_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (chosenDerivedTorsor existence geometry hRigid criterion).val.V.hom =
      (chosenSchemes q).map (smallCMInclusion D hVU) := rfl

@[simp] theorem cmNormalGeometricTorsor_of_dominantCriterion_ρ_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0})
    (g : SmallCMResidualGroup D U V) :
    ((chosenDerivedTorsor existence geometry hRigid criterion).val.ρ g).left =
      (chosenQuotientAction q).ρ g := rfl

@[simp] theorem cmNormalFiniteEtaleAction_of_dominantCriterion_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (chosenDerivedFiniteAction existence geometry hRigid criterion).V.obj.left =
      (chosenSchemes q).obj V := rfl

@[simp] theorem cmNormalFiniteEtaleAction_of_dominantCriterion_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (chosenDerivedFiniteAction existence geometry hRigid criterion).V.obj.hom =
      (chosenSchemes q).map (smallCMInclusion D hVU) := rfl

@[simp] theorem cmNormalFiniteEtaleAction_of_dominantCriterion_ρ_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0})
    (g : SmallCMResidualGroup D U V) :
    ((chosenDerivedFiniteAction existence geometry hRigid criterion).ρ g).hom.left =
      (chosenQuotientAction q).ρ g := rfl

end ChosenIdentifications

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
