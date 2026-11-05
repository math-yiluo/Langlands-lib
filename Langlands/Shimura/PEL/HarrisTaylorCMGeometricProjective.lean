import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-! # Actual projective embeddings and properness of geometric CM levels -/

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

/-- The actual geometric-level morphism induced by a specified original projective
embedding, retaining its dimension. -/
def cmGeometricProjectiveImmersion :
    (geometricSchemes).obj U ⟶ ProjectiveSpace (AlgebraicClosure F) d :=
  ProjectiveSpace.baseChangeLift (squareU U) i hi

local notation "geometricImmersion" => cmGeometricProjectiveImmersion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U i hi

/-- The geometric embedding is a morphism over the algebraic closure itself. -/
@[reassoc (attr := simp)]
theorem cmGeometricProjectiveImmersion_toSpec :
    geometricImmersion ≫ projectiveSpaceToSpec (AlgebraicClosure F) d =
      ((geometricOver).obj U).hom :=
  ProjectiveSpace.baseChangeLift_toSpec (squareU U) i hi

/-- The geometric embedding projects to the unchanged original embedding. -/
@[reassoc (attr := simp)]
theorem cmGeometricProjectiveImmersion_map :
    geometricImmersion ≫ ProjectiveSpace.baseChangeMap F (AlgebraicClosure F) d =
      (projection).app U ≫ i :=
  ProjectiveSpace.baseChangeLift_map (squareU U) i hi

/-- The displayed map on the actual geometric level is the base change of `i`. -/
theorem cmGeometricProjectiveImmersion_isPullback :
    IsPullback ((projection).app U) geometricImmersion i
      (ProjectiveSpace.baseChangeMap F (AlgebraicClosure F) d) :=
  ProjectiveSpace.baseChangeLift_isPullback (squareU U) i hi

/-- The actual geometric-level map is a closed immersion whenever `i` is one. -/
instance cmGeometricProjectiveImmersion_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion geometricImmersion :=
  ProjectiveSpace.baseChangeLift_isClosedImmersion (squareU U) i hi

omit i hi in
/-- The projective witness already contained in the exact representation premise
gives an actual projective witness on the existing geometric level. -/
theorem cmGeometricOverTower_projective :
    IsHProjective ((geometricOver).obj U).hom :=
  (representedCMOverTower_projective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor chosen U).of_isPullback (squareU U)

omit i hi in
/-- The original geometric level is proper over the algebraic closure of the CM field. -/
instance cmGeometricOverTower_isProper :
    IsProper ((geometricOver).obj U).hom :=
  (cmGeometricOverTower_projective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U).isProper

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
