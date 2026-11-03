import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientDivisibleCoherence
import Langlands.Geometry.EtaleDerivedSections
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic

/-! # Derived cohomology of the original CM coefficient tower -/

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

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "X" => Functor.obj (schemes q) U
local notation "J" => Scheme.smallEtaleTopology X
local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

local notation "H" d => EtaleDerivedSections.cohomology X Rcoeff d
local notation "RH" => EtaleDerivedSections.homotopyFunctor X Rcoeff
local notation "shifted" => cmHarrisCoefficientShiftedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "shiftInclusion" => cmHarrisCoefficientShiftInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "shiftReduction" => cmHarrisCoefficientShiftReduction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

local instance cmCohomology_additive (d : ℕ) : (H d).Additive :=
  Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive
    (EtaleDerivedSections.sections X Rcoeff) d

/-- Derived global sections of every original CM coefficient sheaf, with all reductions. -/
def cmHarrisCoefficientDerivedSystem :
    ℕᵒᵖ ⥤ HomotopyCategory (ModuleCat.{0} Rcoeff) (ComplexShape.up ℕ) :=
  system ⋙ RH

/-- Ordinary small-etale cohomology of the actual original CM coefficient system. -/
def cmHarrisCoefficientCohomologySystem (d : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{0} Rcoeff :=
  system ⋙ H d

local notation "cohomologySystem" => cmHarrisCoefficientCohomologySystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "derivedSystem" => cmHarrisCoefficientDerivedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Cohomology transitions are the image of the specified original sheaf reductions. -/
@[simp] theorem cmHarrisCoefficientCohomologySystem_map (d : ℕ)
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (cohomologySystem d).map f = (H d).map ((system).map f) := rfl

/-- The coefficient tower in degree zero is naturally the original global-section tower. -/
def cmHarrisCoefficientCohomologyZeroIso :
    cohomologySystem 0 ≅ system ⋙ EtaleDerivedSections.sections X Rcoeff :=
  Functor.isoWhiskerLeft system (EtaleDerivedSections.cohomologyZeroIso X Rcoeff)

/-- The actual chosen injective-resolution complex represents each derived component. -/
def cmHarrisCoefficientDerivedSystemObjIso (r : ℕᵒᵖ) :
    (derivedSystem).obj r ≅
      (HomotopyCategory.quotient _ _).obj
        (EtaleDerivedSections.complex X Rcoeff ((system).obj r)) :=
  EtaleDerivedSections.complexIso X Rcoeff ((system).obj r)

/-- The resolution computes each actual coefficient cohomology module. -/
def cmHarrisCoefficientCohomologySystemObjIso (d : ℕ) (r : ℕᵒᵖ) :
    (cohomologySystem d).obj r ≅
      (EtaleDerivedSections.complex X Rcoeff ((system).obj r)).homology d :=
  EtaleDerivedSections.cohomologyIso X Rcoeff ((system).obj r) d

/-- Derived cohomology retains each finite-stage annihilating scalar. -/
theorem cmHarrisCoefficientCohomologySystem_powSMul_eq_zero (d r : ℕ) :
    powSMul m r ((cohomologySystem d).obj (op r)) = 0 := by
  change powSMul m r ((H d).obj ((system).obj (op r))) = 0
  rw [← map_powSMul, cmHarrisCoefficientSystem_powSMul_eq_zero, Functor.map_zero]

/-- Apply the cohomology functor to the original shifted coefficient tower. -/
def cmHarrisCoefficientCohomologyShiftedSystem (d k : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{0} Rcoeff := shifted k ⋙ H d

local notation "shiftedCohomology" => cmHarrisCoefficientCohomologyShiftedSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The finite-shift normalized inclusions induce actual cohomology maps. -/
def cmHarrisCoefficientCohomologyShiftInclusion (d k : ℕ) :
    cohomologySystem d ⟶ shiftedCohomology d k :=
  Functor.whiskerRight (shiftInclusion k) (H d)

/-- The original finite-shift reductions induce the reverse cohomology map. -/
def cmHarrisCoefficientCohomologyShiftReduction (d k : ℕ) :
    shiftedCohomology d k ⟶ cohomologySystem d :=
  Functor.whiskerRight (shiftReduction k) (H d)

local notation "cohomologyInclusion" => cmHarrisCoefficientCohomologyShiftInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "cohomologyReduction" => cmHarrisCoefficientCohomologyShiftReduction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The first cohomology composite is the prescribed scalar power on the original tower. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientCohomologyShiftInclusion_reduction
    (d k : ℕ) :
    cohomologyInclusion d k ≫ cohomologyReduction d k =
      powSMul m k (cohomologySystem d) := by
  apply NatTrans.ext
  funext r
  change (H d).map ((shiftInclusion k).app r) ≫
    (H d).map ((shiftReduction k).app r) =
      powSMul m k ((H d).obj ((system).obj r))
  rw [← (H d).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisCoefficientShiftInclusion_reduction D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k)
  change (shiftInclusion k).app r ≫ (shiftReduction k).app r =
    powSMul m k ((system).obj r) at heq
  rw [heq, map_powSMul]

/-- The opposite cohomology composite is the same scalar on the shifted tower. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientCohomologyShiftReduction_inclusion
    (d k : ℕ) :
    cohomologyReduction d k ≫ cohomologyInclusion d k =
      powSMul m k (shiftedCohomology d k) := by
  apply NatTrans.ext
  funext r
  change (H d).map ((shiftReduction k).app r) ≫
    (H d).map ((shiftInclusion k).app r) =
      powSMul m k ((H d).obj ((shifted k).obj r))
  rw [← (H d).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisCoefficientShiftReduction_inclusion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k)
  change (shiftReduction k).app r ≫ (shiftInclusion k).app r =
    powSMul m k ((shifted k).obj r) at heq
  rw [heq, map_powSMul]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
