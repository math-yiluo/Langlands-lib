import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients
import Langlands.Shimura.PEL.HarrisTaylorCMNormalSmoothEtale
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

/-! # Finite-etale normal covers on the actual geometric CM tower -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology
open Langlands.Geometry

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

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "geometricOver" => cmGeometricOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "projection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- Every actual geometric level map is the base change of its original level map. -/
theorem cmGeometricSchemeTower_map_isPullback {U V : SmallCMLevel D} (k : V ⟶ U) :
    IsPullback ((projection).app V) ((geometricSchemes).map k)
      ((schemes).map k) ((projection).app U) := by
  refine IsPullback.of_bot ?_ ((projection).naturality k).symm
    (cmGeometricSchemeTower_isPullback D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U)
  change IsPullback _
    (((geometricOver).map k).left ≫ ((geometricOver).obj U).hom)
    (((overTower).map k).left ≫ ((overTower).obj U).hom) _
  simpa only [Over.w] using
    (cmGeometricSchemeTower_isPullback D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q V)

open Langlands.AlgebraicGeometry.FiniteEtale

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)
  (criterion : DominantUnramifiedEtaleStatement.{0})

include existence geometry hRigid criterion

local notation "originalCover" => cmNormalFiniteEtale_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  U V hVU q existence geometry hRigid criterion
local notation "normalSquare" => cmGeometricSchemeTower_map_isPullback D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q (smallCMInclusion D hVU)
local notation "geometricMap" => (geometricSchemes).map (smallCMInclusion D hVU)

/-- The existing geometric normal projection is etale under the original named criteria. -/
theorem cmGeometricNormalProjection_etale_of_dominantCriterion :
    Etale geometricMap :=
  MorphismProperty.of_isPullback (P := @Etale) normalSquare
    (originalCover).property.2

/-- Finiteness is transported to the same geometric normal projection. -/
theorem cmGeometricNormalProjection_isFinite_of_dominantCriterion :
    IsFinite geometricMap :=
  MorphismProperty.of_isPullback (P := @IsFinite) normalSquare
    (originalCover).property.1

/-- The actual geometric fine level and its normal forgetting map form this cover. -/
def cmGeometricNormalFiniteEtale_of_dominantCriterion :
    Cover ((geometricSchemes).obj U) := by
  have : Etale geometricMap :=
    cmGeometricNormalProjection_etale_of_dominantCriterion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU
      existence geometry hRigid criterion
  have : IsFinite geometricMap :=
    cmGeometricNormalProjection_isFinite_of_dominantCriterion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU
      existence geometry hRigid criterion
  exact cover geometricMap

local notation "geometricCover" => cmGeometricNormalFiniteEtale_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

@[simp] theorem cmGeometricNormalFiniteEtale_of_dominantCriterion_left :
    (geometricCover).obj.left = (geometricSchemes).obj V := rfl

@[simp] theorem cmGeometricNormalFiniteEtale_of_dominantCriterion_hom :
    (geometricCover).obj.hom = geometricMap := rfl

/-- The cover on the existing geometric level is canonically the original cover pulled back. -/
def cmGeometricNormalFiniteEtalePullbackIso :
    geometricCover ≅ (pullbackFunctor ((projection).app U)).obj originalCover :=
  ObjectProperty.isoMk _ (Over.isoMk (normalSquare).isoPullback
    (normalSquare).isoPullback_hom_snd)

local notation "coverIso" => cmGeometricNormalFiniteEtalePullbackIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor
  q U V hVU existence geometry hRigid criterion

/-- The first projection of the canonical comparison is the original geometric projection. -/
@[reassoc (attr := simp)]
theorem cmGeometricNormalFiniteEtalePullbackIso_hom_fst :
    (coverIso).hom.hom.left ≫
      pullback.fst (originalCover).obj.hom ((projection).app U) =
        (projection).app V :=
  (normalSquare).isoPullback_hom_fst

/-- The second projection is exactly the original geometric normal tower map. -/
@[reassoc (attr := simp)]
theorem cmGeometricNormalFiniteEtalePullbackIso_hom_snd :
    (coverIso).hom.hom.left ≫
      pullback.snd (originalCover).obj.hom ((projection).app U) = geometricMap :=
  (normalSquare).isoPullback_hom_snd

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
