import Langlands.AlgebraicGeometry.OpenUnramifiedSmoothEtale
import Langlands.Shimura.PEL.HarrisTaylorCMNormalUnramified
import Langlands.Shimura.PEL.HarrisTaylorCMNormalTopology

/-! # Original CM finite-etale projections from the dominant criterion -/

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
/-- Etaleness of the identical original normal projection, using the named
missing generic criterion and proved original openness and unramifiedness. -/
theorem representedCMNormalProjection_etale_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Etale (projection R U V hVU) := by
  have : Smooth (R V).base.obj.hom := (R V).smooth
  have : Smooth (R U).base.obj.hom := (R U).smooth
  have : FormallyUnramified (projection R U V hVU) :=
    representedCMNormalProjection_formallyUnramified_of_dualGeometry D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid
  exact openUnramifiedSmooth_etale_of_dominantCriterion criterion
    ((schemes R).obj V) ((schemes R).obj U)
    (R V).base.obj.hom (R U).base.obj.hom (projection R U V hVU)
    (representedCMNormalProjection_isOpenMap D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry)

/-- The original normal projection itself, as a finite-etale cover of the
original coarse scheme under the explicit named prerequisites. -/
def representedCMNormalFiniteEtale_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Cover ((schemes R).obj U) := by
  have : Etale (projection R U V hVU) :=
    representedCMNormalProjection_etale_of_dominantCriterion D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      R U V hVU existence geometry hRigid criterion
  exact cover (projection R U V hVU)

local notation "finiteCover" => representedCMNormalFiniteEtale_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor

@[simp] theorem representedCMNormalFiniteEtale_of_dominantCriterion_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (finiteCover R U V hVU existence geometry hRigid criterion).obj.left =
      (schemes R).obj V := rfl

@[simp] theorem representedCMNormalFiniteEtale_of_dominantCriterion_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (finiteCover R U V hVU existence geometry hRigid criterion).obj.hom =
      projection R U V hVU := rfl

local notation "chosenReps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosenSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

/-- The same conclusion for the direct chosen-tower forgetting map. -/
theorem cmNormalProjection_etale_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Etale ((chosenSchemes q).map (smallCMInclusion D hVU)) :=
  representedCMNormalProjection_etale_of_dominantCriterion D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor
    (chosenReps q) U V hVU existence geometry hRigid criterion

/-- The finite-etale cover for the identical representation witnesses used
by `cmSchemeTower`, without an original flatness or etaleness premise. -/
def cmNormalFiniteEtale_of_dominantCriterion
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    Cover ((chosenSchemes q).obj U) :=
  finiteCover (chosenReps q) U V hVU existence geometry hRigid criterion

local notation "chosenFiniteCover" => cmNormalFiniteEtale_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  U V hVU q

@[simp] theorem cmNormalFiniteEtale_of_dominantCriterion_left
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (chosenFiniteCover existence geometry hRigid criterion).obj.left =
      (chosenSchemes q).obj V := rfl

@[simp] theorem cmNormalFiniteEtale_of_dominantCriterion_hom
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (hRigid : Rigid U.obj)
    (criterion : DominantUnramifiedEtaleStatement.{0}) :
    (chosenFiniteCover existence geometry hRigid criterion).obj.hom =
      (chosenSchemes q).map (smallCMInclusion D hVU) := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
