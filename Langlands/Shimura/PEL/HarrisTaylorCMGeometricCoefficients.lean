import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientDivisibleCoherence
import Langlands.Geometry.EtaleInverseImageExact
import Langlands.Geometry.EtaleInverseImageLinear
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric CM scheme levels and their original pulled-back coefficients -/

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

/-- The actual morphism from the algebraic closure of the original CM field. -/
def cmGeometricFieldMap : Spec (.of (AlgebraicClosure F)) ⟶ Spec (.of F) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))).op

/-- Base change of the represented CM tower to the algebraic closure of F. -/
def cmGeometricOverTower : SmallCMLevel D ⥤ Over (Spec (.of (AlgebraicClosure F))) :=
  overTower ⋙ Over.pullback (cmGeometricFieldMap (F := F))

local notation "geometricOver" => cmGeometricOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The actual geometric CM scheme levels and base-changed level maps. -/
def cmGeometricSchemeTower : SmallCMLevel D ⥤ Scheme :=
  geometricOver ⋙ Over.forget (Spec (.of (AlgebraicClosure F)))

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The fiber-product projections commute with every original level map. -/
def cmGeometricProjection : geometricSchemes ⟶ schemes where
  app U := pullback.fst ((overTower).obj U).hom (cmGeometricFieldMap (F := F))
  naturality {U V} k := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp [cmSchemeTower, representedCMSchemeTower]

local notation "projection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- Each level is the genuine scheme fiber product with Spec of the algebraic closure. -/
theorem cmGeometricSchemeTower_isPullback (U : SmallCMLevel D) :
    IsPullback ((projection).app U) ((geometricOver).obj U).hom
      ((overTower).obj U).hom (cmGeometricFieldMap (F := F)) :=
  IsPullback.of_hasPullback _ _

/-- Smoothness of the represented original level is preserved by this base change. -/
instance cmGeometricOverTower_smooth (U : SmallCMLevel D) :
    Smooth ((geometricOver).obj U).hom := by
  change Smooth (pullback.snd ((overTower).obj U).hom (cmGeometricFieldMap (F := F)))
  infer_instance

variable (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "Xbar" => (geometricSchemes).obj U
local notation "geometricPullback" =>
  EtaleInverseImage.inverseImage ((projection).app U) Rcoeff
local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "divisible" => cmHarrisCoefficientDivisibleSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Pull back the original CM coefficient sheaves and every original reduction. -/
def cmHarrisGeometricCoefficientSystem :
    ℕᵒᵖ ⥤ Sheaf (Scheme.smallEtaleTopology Xbar) (ModuleCat.{0} Rcoeff) :=
  system ⋙ geometricPullback

/-- Exact geometric inverse image transports the original divisible-system rows. -/
def cmHarrisGeometricCoefficientDivisibleSystem :
    DivisibleSystem (Sheaf (Scheme.smallEtaleTopology Xbar) (ModuleCat.{0} Rcoeff)) m :=
  (divisible).map geometricPullback

local notation "geometricSystem" => cmHarrisGeometricCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "geometricDivisible" => cmHarrisGeometricCoefficientDivisibleSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The transported divisible system uses exactly the displayed original pullback tower. -/
@[simp] theorem cmHarrisGeometricCoefficientDivisibleSystem_tower :
    (geometricDivisible).tower = geometricSystem := rfl

/-- The geometric inclusion is inverse image of the original cokernel-defined inclusion. -/
@[simp] theorem cmHarrisGeometricCoefficientDivisibleSystem_inclusion
    {r s : ℕ} (hrs : r < s) :
    (geometricDivisible).inclusion hrs =
      (geometricPullback).map ((divisible).inclusion hrs) := rfl

/-- Every geometric transition is inverse image of its specified original reduction. -/
@[simp] theorem cmHarrisGeometricCoefficientSystem_map
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (geometricSystem).map f = (geometricPullback).map ((system).map f) := rfl

/-- The finite-stage annihilation relation holds on the actual geometric sheaf. -/
theorem cmHarrisGeometricCoefficientSystem_powSMul_eq_zero (r : ℕ) :
    powSMul m r ((geometricSystem).obj (op r)) = 0 :=
  (geometricDivisible).powSMul_eq_zero r

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
