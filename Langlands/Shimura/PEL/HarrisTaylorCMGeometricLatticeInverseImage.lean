import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeCoverComparison
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseInverseImage

/-! # Canonical Harris lattice comparison with coarse inverse image -/

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

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigidV : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)
  (hRigidU : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "XV" => (geometricSchemes).obj V
local notation "XU" => (geometricSchemes).obj U
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hVU)
local notation "J" => Scheme.smallEtaleTopology XV
local notation "R" => HarrisCoefficientIntegers K p
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p V m hm
local notation "coefficientInclusion" => cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm
local notation "ownSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V
    ρ p m hm existence geometry hRigidV
local notation "originalSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U
    ρ p m hm existence geometry hRigidU
local notation "coarseSystem" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV
local notation "inverseSystem" => cmHarrisGeometricCoarseInverseImageSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidU
local notation "latticeComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV
local notation "inverseIso" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV hRigidU
local notation "ownCoverIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV
local notation "coarseCoverIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV
local notation "commonCoefficientMap" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV
local notation "commonCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV
local notation "commonOwnInc" k:arg => cmHarrisGeometricLatticeCommonOwnInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV k
local notation "commonOriginalInc" k:arg => cmHarrisGeometricLatticeCommonOriginalInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV k
local notation "ownInc" k:arg => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V
    ρ p m hm existence geometry hRigidV k
local notation "ownCoverMap" k:arg => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV k

/-- Compare the independently constructed V system with inverse image of the original U system. -/
def cmHarrisGeometricLatticeInverseImageComparison : ownSystem ⟶ inverseSystem :=
  latticeComparison ≫ (inverseIso).inv

local notation "inverseComparison" => cmHarrisGeometricLatticeInverseImageComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigidV hRigidU

/-- The component keeps the actual lattice comparison and the constructed inverse-image leg. -/
@[simp] theorem cmHarrisGeometricLatticeInverseImageComparison_app (k : ℕᵒᵖ) :
    (inverseComparison).app k =
      (latticeComparison).app k ≫ (inverseIso).inv.app k := rfl

/-- Its complete component consists of the two cover changes, actual inclusion and inverse image. -/
@[simp] theorem cmHarrisGeometricLatticeInverseImageComparison_app_common (k : ℕᵒᵖ) :
    (inverseComparison).app k =
      ((ownCoverIso).hom.app k ≫ (commonCoefficientMap).app k ≫
        (coarseCoverIso).inv.app k) ≫ (inverseIso).inv.app k := rfl

/-- Every original V reduction commutes with inverse image of the original U reduction. -/
@[reassoc] theorem cmHarrisGeometricLatticeInverseImageComparison_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownSystem).map f ≫ (inverseComparison).app j =
      (inverseComparison).app i ≫
        (inverseImage coarseMap R).map ((originalSystem).map f) :=
  (inverseComparison).naturality f

/-- Returning through the coarse inverse-image isomorphism recovers the actual lattice map. -/
@[reassoc] theorem cmHarrisGeometricLatticeInverseImageComparison_coarse :
    inverseComparison ≫ (inverseIso).hom = latticeComparison := by
  change (latticeComparison ≫ (inverseIso).inv) ≫ (inverseIso).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On the common covers the comparison is precisely association of the original lattice inclusion. -/
@[reassoc] theorem cmHarrisGeometricLatticeInverseImageComparison_common :
    inverseComparison ≫ (inverseIso).hom ≫ (coarseCoverIso).hom =
      (ownCoverIso).hom ≫ commonCoefficientMap := by
  rw [← Category.assoc, cmHarrisGeometricLatticeInverseImageComparison_coarse D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U V
      hVU ρ p m hm existence geometry hRigidV hRigidU]
  exact cmHarrisGeometricLatticeCoefficientComparison_common D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U V
      hVU ρ p m hm existence geometry hRigidV

/-- Component normalization of the same original coefficient map on the common covers. -/
@[reassoc] theorem cmHarrisGeometricLatticeInverseImageComparison_common_app (k : ℕᵒᵖ) :
    (inverseComparison).app k ≫ (inverseIso).hom.app k ≫
        (coarseCoverIso).hom.app k =
      (ownCoverIso).hom.app k ≫ (commonCoefficientMap).app k := by
  have hcommon := congrArg (fun b => b.app k)
    (cmHarrisGeometricLatticeInverseImageComparison_common D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigidV hRigidU)
  simpa only [NatTrans.comp_app] using hcommon

/-- Actual invariant sections pull the own cover coordinate and apply the original coefficient inclusion. -/
@[reassoc] theorem cmHarrisGeometricLatticeInverseImageComparison_inclusion (k : ℕᵒᵖ) :
    (inverseComparison).app k ≫ (inverseIso).hom.app k ≫
        (coarseCoverIso).hom.app k ≫ commonOriginalInc k =
      ownInc k ≫ coverPullback J (ownCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) ≫
        (productSheaf J ((commonCovers).obj.obj k)).map
          ((constantSheaf J (ModuleCat.{0} R)).map ((coefficientInclusion).hom.app k)) := by
  have hcommon := cmHarrisGeometricLatticeInverseImageComparison_common_app D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U V
      hVU ρ p m hm existence geometry hRigidV hRigidU k
  calc
    _ = (ownCoverIso).hom.app k ≫ (commonCoefficientMap).app k ≫
        commonOriginalInc k := by
      simpa only [Category.assoc] using
        congrArg (fun b => b ≫ commonOriginalInc k) hcommon
    _ = (ownCoverIso).hom.app k ≫ commonOwnInc k ≫
        (productSheaf J ((commonCovers).obj.obj k)).map
          ((constantSheaf J (ModuleCat.{0} R)).map ((coefficientInclusion).hom.app k)) := by
      rw [cmHarrisGeometricLatticeCommonCoefficientInclusion_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability
          square universality dualityNaturality polarizationStability compatibility h htor q U V
          hVU ρ p m hm existence geometry hRigidV]
    _ = _ := by
      rw [← Category.assoc,
        cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso_hom_app D C preservation composition unitCoherence associativity comparison symmetry stability
            square universality dualityNaturality polarizationStability compatibility h htor q U V
            hVU ρ p m hm existence geometry hRigidV,
        cmHarrisGeometricLatticeCommonOwnInclusion,
        cmHarrisGeometricLatticeCommonOwnAssociatedComparison_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability
            square universality dualityNaturality polarizationStability compatibility h htor q U V
            hVU ρ p m hm existence geometry hRigidV]
      simp only [cmHarrisGeometricAssociatedCoefficientSystemInclusion, Category.assoc]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
