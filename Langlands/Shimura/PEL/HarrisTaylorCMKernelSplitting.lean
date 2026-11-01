import Langlands.Shimura.PEL.HarrisTaylorCMComponentKernelLift
import Langlands.Shimura.PEL.HarrisTaylorCMFiniteEtale

/-! # Actual splittings of the original CM kernel comparison -/

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

local notation "copies" => representedCMNormalCopies D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelPair" => representedCMNormalKernelPair D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
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
local notation "componentLift" => representedCMNormalKernelComponentLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The actual original kernel pair is locally Noetherian, using original
properness rather than an etaleness hypothesis. -/
instance representedCMNormalKernelPair_locallyNoetherian :
    IsLocallyNoetherian (kernelPair R U V hVU) := by
  have : IsLocallyNoetherian ((schemes R).obj V) := (R V).base.property.locallyNoetherian
  change IsLocallyNoetherian (pullback (projection R U V hVU) (projection R U V hVU))
  infer_instance

/-- An actual section of the original kernel comparison, obtained by lifting
the identity of its actual locally Noetherian target. -/
def representedCMNormalKernelSection
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    kernelPair R U V hVU ⟶ copies R U V :=
  componentLift R U V hVU existence geometry (𝟙 _)

local notation "kernelSection" => representedCMNormalKernelSection D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

@[reassoc (attr := simp)] theorem representedCMNormalKernelSection_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    kernelSection R U V hVU existence geometry ≫ kernelComparison R U V hVU = 𝟙 _ :=
  representedCMNormalKernelComponentLift_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R U V hVU existence geometry (𝟙 _)

/-- The splitting retains precisely the constructed section and original map. -/
def representedCMNormalKernelSplitting
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    SplitEpi (kernelComparison R U V hVU) where
  section_ := kernelSection R U V hVU existence geometry
  id := representedCMNormalKernelSection_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor R U V hVU existence geometry

/-- The original kernel comparison is a split epimorphism without an original
etaleness, rigidity, freeness or monomorphism premise. -/
theorem representedCMNormalKernelComparison_isSplitEpi
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    IsSplitEpi (kernelComparison R U V hVU) :=
  IsSplitEpi.mk' (representedCMNormalKernelSplitting D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    R U V hVU existence geometry)

/-- Postcomposing the explicit section gives lifts for all scheme sources,
with no local Noetherianity assumption on the source. -/
theorem representedCMNormalKernelComparison_allHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (T : Scheme.{0}) :
    Function.Surjective
      (fun d : T ⟶ copies R U V => d ≫ kernelComparison R U V hVU) := by
  intro c
  refine ⟨c ≫ kernelSection R U V hVU existence geometry, ?_⟩
  change (c ≫ kernelSection R U V hVU existence geometry) ≫
    kernelComparison R U V hVU = c
  rw [Category.assoc, representedCMNormalKernelSection_comp, Category.comp_id]

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenComponentLift" => cmNormalKernelComponentLift D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU
local notation "chosenComparison" => cmNormalKernelComparison D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The actual section for exactly the witnesses defining cmSchemeTower. -/
def cmNormalKernelSection
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    kernelPair (chosenReps q) U V hVU ⟶ copies (chosenReps q) U V :=
  kernelSection (chosenReps q) U V hVU existence geometry

local notation "chosenSection" => cmNormalKernelSection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor U V hVU q

/-- The chosen section is literally the existing chosen component lift of the
identity of the original kernel pair. -/
theorem cmNormalKernelSection_eq
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    chosenSection existence geometry = chosenComponentLift q existence geometry (𝟙 _) := rfl

@[reassoc (attr := simp)] theorem cmNormalKernelSection_comp
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    chosenSection existence geometry ≫ chosenComparison q = 𝟙 _ :=
  representedCMNormalKernelSection_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosenReps q) U V hVU existence geometry

/-- A splitting of the identical original chosen kernel comparison. -/
def cmNormalKernelSplitting
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    SplitEpi (chosenComparison q) :=
  representedCMNormalKernelSplitting D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosenReps q) U V hVU existence geometry

theorem cmNormalKernelSplitting_section
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    (cmNormalKernelSplitting D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U V hVU q existence geometry).section_ =
      chosenSection existence geometry := rfl

theorem cmNormalKernelComparison_isSplitEpi
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0}) :
    IsSplitEpi (chosenComparison q) :=
  representedCMNormalKernelComparison_isSplitEpi D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry

/-- Every map into the original chosen kernel pair has a lift for every
universe-zero scheme source, without local Noetherianity. -/
theorem cmNormalKernelComparison_allHom_surjective
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (T : Scheme.{0}) :
    Function.Surjective
      (fun d : T ⟶ copies (chosenReps q) U V => d ≫ chosenComparison q) :=
  representedCMNormalKernelComparison_allHom_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry T

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
