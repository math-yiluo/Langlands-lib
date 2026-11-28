import Langlands.Shimura.PEL.HarrisTaylorCMAnalyticTower
import Langlands.Shimura.PEL.HarrisTaylorCMNormalRefinement
import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Normal-level residual actions on the analytic CM tower -/

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

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra F K]

open Langlands.Analytic.SchemeAnalytification
open Langlands.Analytic.SaturatedAtlasPresentation

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "fieldOver" => cmFieldOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q K
local notation "anTower" => cmFieldAnalyticTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K

/-- Actual analytic transporter maps retain dependence on the original target coset. -/
theorem cmFieldAnalyticTower_map_eq_of_target_coset {U V : SmallCMLevel D} (a b : U ⟶ V)
    (hab : a.hom.element⁻¹ * b.hom.element ∈ V.obj.subgroup) :
    (anTower).map a = (anTower).map b := by
  have hm := representedCMBaseTower_map_eq_of_target_coset D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor chosen a b hab
  apply congrArg ((localizedAnalytification K).map)
  apply ObjectProperty.hom_ext
  change ((fieldOver).map a) = ((fieldOver).map b)
  let baseChange := ObjectProperty.ι
    (ComponentwiseAdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality) ⋙
    Over.pullback (cmFieldExtensionMap (F := F) K)
  exact baseChange.congr_map hm

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "ResidualGroup" => SmallCMResidualGroup D U V
local notation "levelAction" => smallCMNormalLevelAction D U V hVU anTower

private theorem analyticLevelAction_kernel :
    V.obj.subgroup.subgroupOf U.obj.subgroup ≤ (levelAction).ρ.ker := by
  intro g hg
  refine (MonoidHom.mem_ker).mpr (End.ext ?_)
  change (anTower).map (smallCMNormalInverseArrow D U V hVU g) = 𝟙 _
  rw [← (anTower).map_id V]
  apply cmFieldAnalyticTower_map_eq_of_target_coset
  have hg' : (g : OriginalGroup) ∈ V.obj.subgroup := hg
  simpa using hg'

/-- The actual residual quotient acts on the fine analytic level by inverse right transport. -/
def cmFieldAnalyticNormalQuotientAction :
    Action (LocalizedCategory.{0, 0, 0} (K := K)) ResidualGroup where
  V := (anTower).obj V
  ρ := QuotientGroup.lift (V.obj.subgroup.subgroupOf U.obj.subgroup) (levelAction).ρ
    (analyticLevelAction_kernel D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K U V hVU)

local notation "residualAction" => cmFieldAnalyticNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K U V hVU

@[simp]
theorem cmFieldAnalyticNormalQuotientAction_mk (g : U.obj.subgroup) :
    ((residualAction).ρ (QuotientGroup.mk g)).asHom =
      (anTower).map (smallCMNormalInverseArrow D U V hVU g) := rfl

/-- The residual action fixes the actual analytic projection to the coarse level. -/
theorem cmFieldAnalyticNormalProjection_invariant (g : ResidualGroup) :
    ((residualAction).ρ g).asHom ≫ (anTower).map (smallCMInclusion D hVU) =
      (anTower).map (smallCMInclusion D hVU) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    rw [cmFieldAnalyticNormalQuotientAction_mk, ← (anTower).map_comp]
    apply cmFieldAnalyticTower_map_eq_of_target_coset
    change (((g : OriginalGroup)⁻¹ * 1)⁻¹ * 1) ∈ U.obj.subgroup
    simp

/-- The forgetting map is equivariant for the trivial action on the coarse level. -/
def cmFieldAnalyticNormalProjection :
    residualAction ⟶ Action.trivial ResidualGroup ((anTower).obj U) where
  hom := (anTower).map (smallCMInclusion D hVU)
  comm g := by
    simpa using cmFieldAnalyticNormalProjection_invariant D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q K U V hVU g

omit [IsCMField F] [IsScalarTower E F A] [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal] in
/-- The quotient carries its actual discrete quotient topology because the fine level is open. -/
theorem cmAnalyticNormalResidual_discreteTopology : DiscreteTopology ResidualGroup := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact QuotientGroup.discreteTopology
    (Subgroup.subgroupOf_isOpen U.obj.subgroup V.obj.subgroup V.obj.openSubgroup.isOpen)

/-- The analytic fine level with its continuous action of the actual residual quotient. -/
def cmFieldAnalyticNormalGSpace : GSpace.{0, 0, 0} K ResidualGroup :=
  letI := cmAnalyticNormalResidual_discreteTopology D U V
  letI : T2Space (localizedSpaceFunctor.obj (residualAction).V) :=
    cmFieldAnalyticLevel_t2Space D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K V
  ⟨residualAction, GSpace.gSpaceProperty_of_discreteTopology _⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
