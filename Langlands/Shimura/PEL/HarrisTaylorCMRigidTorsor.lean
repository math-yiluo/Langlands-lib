import Langlands.Shimura.PEL.HarrisTaylorCMNormalTorsor
import Langlands.Shimura.PEL.HarrisTaylorCMKernelIsomorphism

/-! # The original CM finite geometric torsor under coarse-object rigidity -/

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


variable {L : Type} [Field L] [NumberField L] [IsCMField L]
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


local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "etaleAction" => representedCMNormalEtaleAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

local notation "Rigid" => CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-- Coarse-object rigidity derives the exact kernel-isomorphism premise of the
original torsor adapter. Original projection etaleness remains explicit. -/
theorem representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_rigidity
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)] :
    Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U)
      (etaleAction R U V hVU) := by
  have : IsIso (kernelComparison R U V hVU) :=
    representedCMNormalKernelComparison_isIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor R U V hVU
      existence geometry hRigid
  exact representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry

/-- The original action with its derived finite geometric torsor proof, without
an input asserting invertibility of its kernel comparison. -/
def representedCMNormalGeometricTorsorOfRigidity
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection R U V hVU)] :
    {Y : Action ((schemes R).obj U).Etale (SmallCMResidualGroup D U V) //
      Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U) Y} :=
  ⟨etaleAction R U V hVU,
    representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_rigidity D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid⟩

local notation "rigidTorsor" => representedCMNormalGeometricTorsorOfRigidity D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor

section Identifications

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

/-- The value is precisely the existing original small-etale action. -/
@[simp] theorem representedCMNormalGeometricTorsorOfRigidity_val
    (hRigid : Rigid U.obj) [Etale (projection R U V hVU)] :
    (rigidTorsor R U V hVU existence geometry hRigid).val =
      etaleAction R U V hVU := rfl

/-- Its source is the original fine-level scheme. -/
@[simp] theorem representedCMNormalGeometricTorsorOfRigidity_left
    (hRigid : Rigid U.obj) [Etale (projection R U V hVU)] :
    (rigidTorsor R U V hVU existence geometry hRigid).val.V.left =
      (schemes R).obj V := rfl

/-- Its structural map is exactly original forgetting. -/
@[simp] theorem representedCMNormalGeometricTorsorOfRigidity_hom
    (hRigid : Rigid U.obj) [Etale (projection R U V hVU)] :
    (rigidTorsor R U V hVU existence geometry hRigid).val.V.hom =
      projection R U V hVU := rfl

/-- Each action map remains the original inverse-right residual translation. -/
@[simp] theorem representedCMNormalGeometricTorsorOfRigidity_ρ_left
    (hRigid : Rigid U.obj) [Etale (projection R U V hVU)]
    (g : SmallCMResidualGroup D U V) :
    ((rigidTorsor R U V hVU existence geometry hRigid).val.ρ g).left =
      (quotientAction R U V hVU).ρ g := rfl

end Identifications

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "chosenEtaleAction" => cmNormalEtaleAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q
local notation "chosenSchemes" => cmSchemeTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q

/-- The original chosen action satisfies the same finite geometric torsor
predicate under original etaleness and explicit coarse-object rigidity. -/
theorem cmNormalEtaleAction_isFiniteGeometricTorsor_of_rigidity
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection chosen U V hVU)] :
    Coefficients.IsFiniteGeometricTorsor ((chosenSchemes).obj U) chosenEtaleAction :=
  representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_rigidity D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    chosen U V hVU existence geometry hRigid

/-- The torsor on exactly the witnesses defining `cmSchemeTower`, with no
separate kernel-comparison invertibility input. -/
def cmNormalGeometricTorsorOfRigidity
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    [Etale (projection chosen U V hVU)] :
    {Y : Action ((chosenSchemes).obj U).Etale (SmallCMResidualGroup D U V) //
      Coefficients.IsFiniteGeometricTorsor ((chosenSchemes).obj U) Y} :=
  rigidTorsor chosen U V hVU existence geometry hRigid

local notation "chosenRigidTorsor" => cmNormalGeometricTorsorOfRigidity D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  U V hVU q

section ChosenIdentifications

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

/-- The chosen value is the pre-existing chosen CM small-etale action. -/
@[simp] theorem cmNormalGeometricTorsorOfRigidity_val
    (hRigid : Rigid U.obj) [Etale (projection chosen U V hVU)] :
    (chosenRigidTorsor existence geometry hRigid).val = chosenEtaleAction := rfl

/-- The chosen source is the original chosen fine-level scheme. -/
@[simp] theorem cmNormalGeometricTorsorOfRigidity_left
    (hRigid : Rigid U.obj) [Etale (projection chosen U V hVU)] :
    (chosenRigidTorsor existence geometry hRigid).val.V.left =
      (chosenSchemes).obj V := rfl

/-- The chosen structural map is the original chosen tower transition. -/
@[simp] theorem cmNormalGeometricTorsorOfRigidity_hom
    (hRigid : Rigid U.obj) [Etale (projection chosen U V hVU)] :
    (chosenRigidTorsor existence geometry hRigid).val.V.hom =
      (chosenSchemes).map (smallCMInclusion D hVU) := rfl

/-- The chosen action maps are precisely the original chosen residual maps. -/
@[simp] theorem cmNormalGeometricTorsorOfRigidity_ρ_left
    (hRigid : Rigid U.obj) [Etale (projection chosen U V hVU)]
    (g : SmallCMResidualGroup D U V) :
    ((chosenRigidTorsor existence geometry hRigid).val.ρ g).left =
      (cmNormalQuotientAction D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q).ρ g := rfl

end ChosenIdentifications

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
