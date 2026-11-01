import Langlands.Shimura.PEL.HarrisTaylorCMFiniteEtale
import Langlands.Shimura.PEL.HarrisTaylorCMSchemeSurjectivity

/-! # The original CM normal action as a finite geometric torsor -/

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

/-- Projectivity proves finiteness and the named dual assertions prove
surjectivity for this original normal action. -/
theorem representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    [Etale (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)] :
    Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U)
      (etaleAction R U V hVU) := by
  apply representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_projective D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    R U V hVU
  exact representedCMSchemeTower_map_surjective D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R existence geometry
    (smallCMInclusion D hVU)

/-- The original small-etale residual action together with its derived proof
of the existing finite geometric torsor predicate. -/
def representedCMNormalGeometricTorsor
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    [Etale (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)] :
    {Y : Action ((schemes R).obj U).Etale (SmallCMResidualGroup D U V) //
      Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U) Y} :=
  ⟨etaleAction R U V hVU,
    representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry⟩

local notation "torsor" => representedCMNormalGeometricTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

section Identifications

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

/-- The bundled action is the previously constructed original etale action. -/
@[simp] theorem representedCMNormalGeometricTorsor_val
    [Etale (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)] :
    (torsor R U V hVU existence geometry).val = etaleAction R U V hVU := rfl

/-- Its source remains exactly the original fine-level scheme. -/
@[simp] theorem representedCMNormalGeometricTorsor_left
    [Etale (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)] :
    (torsor R U V hVU existence geometry).val.V.left = (schemes R).obj V := rfl

/-- Its structural map remains exactly original forgetting. -/
@[simp] theorem representedCMNormalGeometricTorsor_hom
    [Etale (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)] :
    (torsor R U V hVU existence geometry).val.V.hom = projection R U V hVU := rfl

/-- Each underlying action map is the original inverse-right residual translation. -/
@[simp] theorem representedCMNormalGeometricTorsor_ρ_left
    [Etale (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)]
    (g : SmallCMResidualGroup D U V) :
    ((torsor R U V hVU existence geometry).val.ρ g).left =
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

/-- The identical chosen witnesses defining the CM scheme tower satisfy the
existing torsor predicate under the two remaining exact cover premises. -/
theorem cmNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    [Etale (projection chosen U V hVU)]
    [IsIso (kernelComparison chosen U V hVU)] :
    Coefficients.IsFiniteGeometricTorsor ((schemes chosen).obj U) chosenEtaleAction :=
  representedCMNormalEtaleAction_isFiniteGeometricTorsor_of_dualGeometry D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor
    chosen U V hVU existence geometry

/-- The finite geometric torsor on the exact schemes chosen from the existing
CM representability statement. -/
def cmNormalGeometricTorsor
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    [Etale (projection chosen U V hVU)]
    [IsIso (kernelComparison chosen U V hVU)] :
    {Y : Action ((cmSchemeTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q).obj U).Etale
        (SmallCMResidualGroup D U V) //
      Coefficients.IsFiniteGeometricTorsor
        ((cmSchemeTower D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q).obj U) Y} :=
  torsor chosen U V hVU existence geometry

/-- The chosen torsor has exactly the existing CM small-etale action. -/
@[simp] theorem cmNormalGeometricTorsor_val
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    [Etale (projection chosen U V hVU)]
    [IsIso (kernelComparison chosen U V hVU)] :
    (cmNormalGeometricTorsor D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U V hVU q existence geometry).val =
        chosenEtaleAction := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
