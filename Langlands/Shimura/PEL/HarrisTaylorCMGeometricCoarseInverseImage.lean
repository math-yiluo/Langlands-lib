import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseAssociatedSystem
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem
import Langlands.Shimura.Coefficients.EtaleInverseImageVaryingSystem

/-! # Coarse inverse image of the original geometric Harris coefficient system -/

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
open Langlands.Geometry Langlands.Geometry.EtaleInverseImage

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

local notation "originalProperty" =>
  cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigidU
local notation "originalSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigidU
local notation "originalInc" k:arg => cmHarrisGeometricAssociatedCoefficientSystemInclusion
  D C preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigidU k
local notation "system" => cmHarrisGeometricCoarseAssociatedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV
local notation "inc" k:arg => cmHarrisGeometricCoarseAssociatedInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV k
local notation "comparisonMap" k:arg => cmHarrisGeometricCoarseAssociatedComparison D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU k
local notation "coverSystemIso" => cmHarrisGeometricCoarseAssociatedCoverIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU

/-- Genuine small-etale inverse image of the full original geometric coefficient system. -/
def cmHarrisGeometricCoarseInverseImageSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  originalSystem ⋙ inverseImage coarseMap R

local notation "inverseSystem" => cmHarrisGeometricCoarseInverseImageSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidU

/-- Each component is inverse image of the original associated sheaf at U. -/
@[simp] theorem cmHarrisGeometricCoarseInverseImageSystem_obj (k : ℕᵒᵖ) :
    (inverseSystem).obj k = (inverseImage coarseMap R).obj ((originalSystem).obj k) := rfl

/-- Every transition is inverse image of the unchanged original exponent transition. -/
@[simp] theorem cmHarrisGeometricCoarseInverseImageSystem_map
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (inverseSystem).map f = (inverseImage coarseMap R).map ((originalSystem).map f) := rfl

/-- Coarse inverse image agrees with association on the actual intersection covers,
with the original full lattice and all its reductions. -/
def cmHarrisGeometricCoarseInverseImageAssociatedIso : inverseSystem ≅ system :=
  (etaleAssociatedVaryingSystemInverseImage coarseMap R originalCovers originalProperty).app
    originalCoefficients ≪≫ coverSystemIso

local notation "systemIso" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
  existence geometry hRigidV hRigidU

/-- The forward component uses arbitrary-morphism inverse image and the actual
intersection-to-pullback cover comparison under the residual embedding. -/
@[simp] theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_hom_app (k : ℕᵒᵖ) :
    (systemIso).hom.app k =
      (inverseImageConstantAssociatedIso coarseMap R ((originalCovers).action k)
        (originalProperty k)).hom.app ((originalCoefficients).action k) ≫ comparisonMap k := rfl

/-- The inverse reverses the two constructed isomorphisms. -/
@[simp] theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_inv_app (k : ℕᵒᵖ) :
    (systemIso).inv.app k = (coverSystemIso).inv.app k ≫
      (inverseImageConstantAssociatedIso coarseMap R ((originalCovers).action k)
        (originalProperty k)).inv.app ((originalCoefficients).action k) := rfl

/-- The comparison commutes with inverse image of every original reduction. -/
@[reassoc] theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (inverseImage coarseMap R).map ((originalSystem).map f) ≫ (systemIso).hom.app j =
      (systemIso).hom.app i ≫ (system).map f :=
  (systemIso).hom.naturality f

/-- The inverse comparison commutes with every actual intersection-system transition. -/
@[reassoc] theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (system).map f ≫ (systemIso).inv.app j =
      (systemIso).inv.app i ≫ (inverseImage coarseMap R).map ((originalSystem).map f) :=
  (systemIso).inv.naturality f

/-- The actual coarse inverse-image comparison has its specified normalization on
invariant sections, including product, constant and intersection cover coordinates. -/
@[reassoc] theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_hom_inclusion
    (k : ℕᵒᵖ) :
    (systemIso).hom.app k ≫ inc k =
      (inverseImage coarseMap R).map (originalInc k) ≫
        (inverseImageProductSheafIso coarseMap R ((originalCovers).action k)
          (originalProperty k)
          ((constantSheaf (Scheme.smallEtaleTopology XU) (ModuleCat.{0} R)).obj
            ((originalCoefficients).obj.obj k))).hom ≫
        (productSheaf J ((pulledCovers).obj.obj k)).map
          ((inverseImageConstantIso coarseMap R).hom.app ((originalCoefficients).obj.obj k)) ≫
        coverPullback J (coverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) := by
  change ((inverseImageConstantAssociatedIso coarseMap R ((originalCovers).action k)
    (originalProperty k)).hom.app ((originalCoefficients).action k) ≫
      (coverSystemIso).hom.app k) ≫ inc k = _
  rw [Category.assoc, cmHarrisGeometricCoarseAssociatedCoverIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm
    existence geometry hRigidV hRigidU k]
  exact inverseImageConstantAssociatedIso_hom_inclusion_assoc coarseMap R
    ((originalCovers).action k) (originalProperty k) ((originalCoefficients).action k) _

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
