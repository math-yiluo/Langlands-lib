import Langlands.Shimura.PEL.HarrisTaylorCMFieldBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMHeckeSchemes
import Langlands.Geometry.Analytic.SchemeAnalytificationLocalizedFunctor
import Langlands.Geometry.Analytic.SeparatedAnalytificationForward
import Langlands.Geometry.Analytic.QuasiEtaleCompactProbeTopology
import Langlands.Global.AdelicSpaceLocalFields
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-! # Analytic spaces and Hecke maps of the local represented CM tower -/

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

local notation "fieldOver" => cmFieldOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The local field base-changed levels are separated over the new field. -/
theorem cmFieldOverTower_isSeparated (U : SmallCMLevel D) :
    IsSeparated ((fieldOver).obj U).hom := by
  let chosen := chosenCMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q
  let : IsProper (chosen U).base.obj.hom := IsHProjective.isProper (chosen U).projective
  change IsSeparated (pullback.snd (chosen U).base.obj.hom (cmFieldExtensionMap (F := F) K))
  infer_instance

/-- The base-changed represented levels as separated schemes locally of finite type. -/
def cmFieldSeparatedTower :
    SmallCMLevel D ⥤ (separatedLocallyFiniteTypeOver K).FullSubcategory :=
  (separatedLocallyFiniteTypeOver K).lift fieldOver (fun U => ⟨inferInstance,
    cmFieldOverTower_isSeparated D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q K U⟩)

/-- Analytification of every base-changed represented level and its original transporter maps. -/
def cmFieldAnalyticTower : SmallCMLevel D ⥤ LocalizedCategory.{0, 0, 0} (K := K) :=
  cmFieldSeparatedTower D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q K ⋙ localizedAnalytification K

local notation "anTower" => cmFieldAnalyticTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K

/-- The analytic space of each represented level is Hausdorff. -/
theorem cmFieldAnalyticLevel_t2Space (U : SmallCMLevel D) :
    T2Space (localizedSpaceFunctor.obj ((anTower).obj U)) := by
  let : LocallyOfFiniteType ((fieldOver).obj U).hom := inferInstance
  let : IsSeparated ((fieldOver).obj U).hom := cmFieldOverTower_isSeparated D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q K U
  exact SeparatedForward.t2Space_of_isSeparated K ((fieldOver).obj U).hom

/-- The small analytic étale topology on the actual analytification at a fixed CM level. -/
abbrev cmFieldAnalyticEtaleTopology (U : SmallCMLevel D) := etaleTopology ((anTower).obj U)

/-- The compact-probe quasi-étale topology on the same analytic level. -/
abbrev cmFieldAnalyticQuasiEtaleTopology (U : SmallCMLevel D) :=
  compactProbeQuasiEtaleTopology ((anTower).obj U)

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

/-- The analytic first leg of a Hecke span from the original intersection level. -/
def cmFieldAnalyticHeckeLeft (U V : SmallCMLevel D) (g : OriginalGroup) :
    (anTower).obj (smallCMHeckeLevel D U V g) ⟶ (anTower).obj U :=
  (anTower).map (smallCMHeckeLeft D U V g)

/-- The analytic second leg, induced by the original right transporter. -/
def cmFieldAnalyticHeckeRight (U V : SmallCMLevel D) (g : OriginalGroup) :
    (anTower).obj (smallCMHeckeLevel D U V g) ⟶ (anTower).obj V :=
  (anTower).map (smallCMHeckeRight D U V g)

local notation "leftLeg" => cmFieldAnalyticHeckeLeft D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K
local notation "rightLeg" => cmFieldAnalyticHeckeRight D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q K

/-- Refining the levels gives a commuting square of first legs in the analytic category. -/
theorem cmFieldAnalyticHeckeRefinement_left {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup) (hV : V'.obj.subgroup ≤ V.obj.subgroup)
    (g : OriginalGroup) :
    (anTower).map (smallCMHeckeRefinement D hU hV g) ≫ leftLeg U V g =
      leftLeg U' V' g ≫ (anTower).map (smallCMInclusion D hU) := by
  change (anTower).map _ ≫ (anTower).map _ = (anTower).map _ ≫ (anTower).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallCMHeckeRefinement_left]

/-- Refining the levels gives a commuting square of translating legs. -/
theorem cmFieldAnalyticHeckeRefinement_right {U' V' U V : SmallCMLevel D}
    (hU : U'.obj.subgroup ≤ U.obj.subgroup) (hV : V'.obj.subgroup ≤ V.obj.subgroup)
    (g : OriginalGroup) :
    (anTower).map (smallCMHeckeRefinement D hU hV g) ≫ rightLeg U V g =
      rightLeg U' V' g ≫ (anTower).map (smallCMInclusion D hV) := by
  change (anTower).map _ ≫ (anTower).map _ = (anTower).map _ ≫ (anTower).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallCMHeckeRefinement_right]

open scoped NumberField

/-- The analytic CM tower at the canonical completion of the chosen finite place. -/
abbrev cmLocalAnalyticTower (v : Global.FinitePlace F) :
    SmallCMLevel D ⥤ @LocalizedCategory.{0, 0, 0} (Global.FiniteCompletion F v)
      (Global.AdelicSpaceLocalFields.normedField (𝓞 F) F v).toNormedField
      (Global.AdelicSpaceLocalFields.isUltrametricDist (𝓞 F) F v)
      (Global.AdelicSpaceLocalFields.completeSpace (𝓞 F) F v) :=
  letI := Global.AdelicSpaceLocalFields.normedField (𝓞 F) F v
  letI := Global.AdelicSpaceLocalFields.isUltrametricDist (𝓞 F) F v
  letI := Global.AdelicSpaceLocalFields.completeSpace (𝓞 F) F v
  cmFieldAnalyticTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q (Global.FiniteCompletion F v)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
