import Langlands.Shimura.PEL.HarrisTaylorCMGeometricProjective
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGalois
import Langlands.AlgebraicGeometry.ProjectiveSpace.GaloisAction

/-! # Equivariance of the actual geometric CM projective embeddings -/

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
local notation "squareU" => cmGeometricSchemeTower_isPullback D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable (U : SmallCMLevel D) {d : ℕ}
  (i : (cmSchemeTower D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q).obj U ⟶ ProjectiveSpace F d)
  (hi : i ≫ projectiveSpaceToSpec F d =
    ((representedCMOverTower D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor
      (chosenCMLevelRepresentation D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q)).obj U).hom)

local notation "geometricImmersion" => cmGeometricProjectiveImmersion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U i hi
local notation "galoisMap" => cmGeometricGaloisMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "galoisAction" => cmGeometricGaloisAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The original geometric projective map intertwines the actual raw Galois
maps on its source and on its specified projective target. -/
theorem cmGeometricProjectiveImmersion_galoisMap
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    (galoisMap σ).app U ≫ geometricImmersion =
      geometricImmersion ≫ ProjectiveSpace.galoisMap F (AlgebraicClosure F) d σ := by
  exact ProjectiveSpace.baseChangeLift_galoisMap (squareU U) i hi σ _
    (cmGeometricGaloisMap_app_projection D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q σ U)
    (cmGeometricGaloisMap_app_structure D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q σ U)

/-- The same geometric map intertwines the inverse-comorphism left actions. -/
theorem cmGeometricProjectiveImmersion_galoisAction
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    ((galoisAction) σ).hom.app U ≫ geometricImmersion =
      geometricImmersion ≫
        (ProjectiveSpace.galoisAction F (AlgebraicClosure F) d σ).hom := by
  simpa only [cmGeometricGaloisAction_hom, ProjectiveSpace.galoisAction_hom] using
    cmGeometricProjectiveImmersion_galoisMap D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U i hi σ⁻¹

/-- Equivariance also holds for the existing bundled action evaluated at a level. -/
theorem cmGeometricProjectiveImmersion_galoisLevelAction
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    (cmGeometricGaloisLevelAction D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U σ).hom ≫ geometricImmersion =
      geometricImmersion ≫
        (ProjectiveSpace.galoisAction F (AlgebraicClosure F) d σ).hom := by
  change ((galoisAction) σ).hom.app U ≫ geometricImmersion = _
  exact cmGeometricProjectiveImmersion_galoisAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U i hi σ

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
