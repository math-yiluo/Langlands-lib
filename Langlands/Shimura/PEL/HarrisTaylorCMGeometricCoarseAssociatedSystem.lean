import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseRestriction
import Langlands.Shimura.Coefficients.VaryingSystemCoverChange

/-! # Harris associated coefficient systems on actual coarse intersection covers -/

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

local notation "fieldProjection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

local notation "levels" => cmHarrisCoarseCoefficientLevels D ρ p U V hVU m hm
local notation "groups" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "T" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k
local notation "hT" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U V hVU m hm k
local notation "originalT" k:arg => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "originalhT" k:arg => cmHarrisCoefficientLevel_le D ρ p U m hm k
local notation "hOriginal" k:arg =>
  cmHarrisCoarseCoefficientLevel_le_original D ρ p U V hVU m hm k
local notation "hincl" f:arg =>
  cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom (f).unop)
local notation "originalGroups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "groupInclusion" k:arg =>
  cmHarrisCoarseCoefficientGroupInclusion D ρ p U V hVU m hm k
local notation "XV" => (geometricSchemes).obj V
local notation "XU" => (geometricSchemes).obj U
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hVU)
local notation "geometricAction" k:arg => cmGeometricNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q V (T k) (hT k)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigidV : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)
  (hRigidU : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "J" => Scheme.smallEtaleTopology XV
local notation "R" => HarrisCoefficientIntegers K p
local notation "coefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm
local notation "originalCoefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV
local notation "coverProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U V
  hVU ρ p m hm existence geometry hRigidV
local notation "originalCovers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigidU
local notation "pulledCovers" =>
  (etaleTorsorDiagramPullback coarseMap originalGroups).obj originalCovers
local notation "pulledProperty" => cmHarrisGeometricCoarsePulledDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U V
  hVU ρ p m hm existence geometry hRigidU
local notation "coverMap" k:arg => cmHarrisGeometricCoarsePullbackCoverMap D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU k
local notation "actionMap" k:arg => cmHarrisGeometricCoarsePullbackActionMap D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU k

/-- The original full lattice reductions associated on actual V-intersection torsors. -/
def cmHarrisGeometricCoarseAssociatedSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  etaleAssociatedVaryingSystem XV covers coverProperty coefficients

local notation "system" => cmHarrisGeometricCoarseAssociatedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV

/-- Each component uses the actual intersection cover and restricted original action. -/
@[simp] theorem cmHarrisGeometricCoarseAssociatedSystem_obj (k : ℕᵒᵖ) :
    (system).obj k =
      (etaleAssociatedFunctor XV ((covers).action k)).obj ((coefficients).action k) := rfl

/-- The exponent transition uses original reduction and inverse cover comparison. -/
@[simp] theorem cmHarrisGeometricCoarseAssociatedSystem_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f = (etaleAssociatedReduction XV covers f).app coefficients ≫
      (etaleAssociatedComparisonIso XV covers coverProperty f).inv.app coefficients := rfl

/-- Invariant inclusion on the named intersection cover, retaining integral scalars. -/
def cmHarrisGeometricCoarseAssociatedInclusion (k : ℕᵒᵖ) :
    (system).obj k ⟶ (productSheaf J ((covers).obj.obj k)).obj
      ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  etaleAssociatedInclusion XV ((covers).action k) ((coefficients).action k)

local notation "inc" k:arg => cmHarrisGeometricCoarseAssociatedInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV k

instance cmHarrisGeometricCoarseAssociatedInclusion_mono (k : ℕᵒᵖ) : Mono (inc k) :=
  etaleAssociatedInclusion_mono XV ((covers).action k) ((coefficients).action k)

/-- Normalization of all exponent transitions on original coefficient-valued sections. -/
@[reassoc] theorem cmHarrisGeometricCoarseAssociatedSystem_map_inclusion
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ inc j ≫ coverPullback J ((covers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj j)) =
      inc i ≫ (productSheaf J ((covers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((coefficients).obj.map f)) :=
  etaleAssociatedTransition_inclusion XV covers coverProperty f coefficients

/-- The system associated to the literal pullbacks of the original G-torsors. -/
def cmHarrisGeometricCoarsePulledAssociatedSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  etaleAssociatedVaryingSystem XV pulledCovers pulledProperty originalCoefficients

local notation "pulledSystem" => cmHarrisGeometricCoarsePulledAssociatedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidU
local notation "pulledInc" k:arg =>
  etaleAssociatedInclusion XV ((pulledCovers).action k) ((originalCoefficients).action k)

/-- The component comparison is constructed from the actual cover map and coefficient identity. -/
def cmHarrisGeometricCoarseAssociatedComparison (k : ℕᵒᵖ) :
    (pulledSystem).obj k ⟶ (system).obj k :=
  etaleCrossCoverMap XV (groupInclusion k) (actionMap k)
    (𝟙 ((Action.res (ModuleCat.{0} R) (groupInclusion k)).obj
      ((originalCoefficients).action k)))

local notation "comparisonMap" k:arg => cmHarrisGeometricCoarseAssociatedComparison D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU k

/-- The comparison is invertible, even when the residual embedding is not surjective. -/
theorem cmHarrisGeometricCoarseAssociatedComparison_isIso (k : ℕᵒᵖ) :
    IsIso (comparisonMap k) :=
  etaleAssociatedCoverComparison XV ((originalGroups).obj k) ((groups).obj k)
    ((pulledCovers).action k) ((covers).action k) (pulledProperty k) (coverProperty k)
    (groupInclusion k) (actionMap k) R ((originalCoefficients).action k)

/-- The comparison changes the actual cover coordinate and keeps the original coefficient. -/
@[reassoc] theorem cmHarrisGeometricCoarseAssociatedComparison_inclusion (k : ℕᵒᵖ) :
    comparisonMap k ≫ inc k =
      pulledInc k ≫ coverPullback J (coverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) :=
  etaleCrossCoverMap_identity_inclusion XV R
    (A := (pulledCovers).action k) (B := (covers).action k)
    (groupInclusion k) (actionMap k) ((originalCoefficients).action k)

/-- The component comparisons commute with every original exponent reduction. -/
@[reassoc] theorem cmHarrisGeometricCoarseAssociatedComparison_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (pulledSystem).map f ≫ comparisonMap j = comparisonMap i ≫ (system).map f := by
  have hcover :
      coverPullback J (coverMap j)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) ≫
        coverPullback J ((covers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) =
      coverPullback J ((pulledCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) ≫
        coverPullback J (coverMap i)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) := by
    rw [← coverPullback_comp, ← coverPullback_comp]
    exact congrArg (fun a => coverPullback J a
      ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)))
      (cmHarrisGeometricCoarsePullbackCoverMap_naturality D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
        existence geometry hRigidV hRigidU f)
  have hpulled :
      (pulledSystem).map f ≫ pulledInc j ≫
        coverPullback J ((pulledCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) =
      pulledInc i ≫ (productSheaf J ((pulledCovers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((originalCoefficients).obj.map f)) :=
    etaleAssociatedTransition_inclusion XV pulledCovers pulledProperty f originalCoefficients
  have hcoarse :
      (system).map f ≫ inc j ≫ coverPullback J ((covers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) =
      inc i ≫ (productSheaf J ((covers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((originalCoefficients).obj.map f)) :=
    etaleAssociatedTransition_inclusion XV covers coverProperty f coefficients
  apply etaleAssociatedTransition_hom_ext XV covers coverProperty f coefficients
  simp only [Category.assoc]
  change (pulledSystem).map f ≫ comparisonMap j ≫ inc j ≫
      coverPullback J ((covers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j)) =
    comparisonMap i ≫ (system).map f ≫ inc j ≫
      coverPullback J ((covers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j))
  rw [cmHarrisGeometricCoarseAssociatedComparison_inclusion_assoc D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
      existence geometry hRigidV hRigidU j, hcoarse,
    cmHarrisGeometricCoarseAssociatedComparison_inclusion_assoc D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
      existence geometry hRigidV hRigidU i, hcover]
  have hpulled' := congrArg (fun a => a ≫ coverPullback J (coverMap i)
    ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj j))) hpulled
  simpa only [Category.assoc, coverPullback_natural] using hpulled'

/-- The whole associated systems agree on all original lattice exponents. -/
def cmHarrisGeometricCoarseAssociatedCoverIso : pulledSystem ≅ system :=
  NatIso.ofComponents (fun k => by
    letI := cmHarrisGeometricCoarseAssociatedComparison_isIso D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
      existence geometry hRigidV hRigidU k
    exact asIso (comparisonMap k))
    (fun f => cmHarrisGeometricCoarseAssociatedComparison_naturality D C preservation
      composition unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
      existence geometry hRigidV hRigidU f)

local notation "coverSystemIso" => cmHarrisGeometricCoarseAssociatedCoverIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU

/-- Its component is the specified cross-cover map under the residual embedding. -/
@[simp] theorem cmHarrisGeometricCoarseAssociatedCoverIso_hom_app (k : ℕᵒᵖ) :
    (coverSystemIso).hom.app k = comparisonMap k := rfl

/-- The forward system comparison retains all exponent transition maps. -/
@[reassoc] theorem cmHarrisGeometricCoarseAssociatedCoverIso_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (pulledSystem).map f ≫ (coverSystemIso).hom.app j =
      (coverSystemIso).hom.app i ≫ (system).map f :=
  (coverSystemIso).hom.naturality f

/-- The inverse comparison retains all exponent transition maps. -/
@[reassoc] theorem cmHarrisGeometricCoarseAssociatedCoverIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ (coverSystemIso).inv.app j =
      (coverSystemIso).inv.app i ≫ (pulledSystem).map f :=
  (coverSystemIso).inv.naturality f

/-- The whole-system isomorphism has the exact original cover-coordinate normalization. -/
@[reassoc] theorem cmHarrisGeometricCoarseAssociatedCoverIso_hom_inclusion (k : ℕᵒᵖ) :
    (coverSystemIso).hom.app k ≫ inc k =
      pulledInc k ≫ coverPullback J (coverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) :=
  cmHarrisGeometricCoarseAssociatedComparison_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
    existence geometry hRigidV hRigidU k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
