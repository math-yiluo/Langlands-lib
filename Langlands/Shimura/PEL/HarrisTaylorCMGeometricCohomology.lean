import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients
import Langlands.Geometry.EtaleDerivedSections
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic

/-! # Finite shifts and cohomology of the geometric CM coefficient tower -/

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

local notation "schemes" => cmGeometricSchemeTower D C preservation composition
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
local notation "system" => cmHarrisGeometricCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

local notation "geometricPullback" => EtaleInverseImage.inverseImage
  ((cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q).app U) Rcoeff
local notation "originalSystem" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalShifted" => cmHarrisCoefficientShiftedSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalInclusion" => cmHarrisCoefficientShiftInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalReduction" => cmHarrisCoefficientShiftReduction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalInclusionLE" => cmHarrisCoefficientInclusionLE D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Pull back the original finite shift, retaining every original reduction. -/
def cmHarrisGeometricCoefficientShiftedSystem (k : ℕ) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} Rcoeff) :=
  originalShifted k ⋙ geometricPullback

local notation "shifted" => cmHarrisGeometricCoefficientShiftedSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The geometric finite shift has exactly the original exponent plus the shift. -/
@[simp] theorem cmHarrisGeometricCoefficientShiftedSystem_obj (k : ℕ) (r : ℕᵒᵖ) :
    (shifted k).obj r = (system).obj (op (r.unop + k)) := rfl

/-- Transport the original normalized inclusion by the actual geometric inverse image. -/
def cmHarrisGeometricCoefficientShiftInclusion (k : ℕ) : system ⟶ shifted k :=
  Functor.whiskerRight (originalInclusion k) geometricPullback

/-- Transport the specified original finite-shift reduction by the same inverse image. -/
def cmHarrisGeometricCoefficientShiftReduction (k : ℕ) : shifted k ⟶ system :=
  Functor.whiskerRight (originalReduction k) geometricPullback

local notation "shiftInclusion" => cmHarrisGeometricCoefficientShiftInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "shiftReduction" => cmHarrisGeometricCoefficientShiftReduction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Each geometric inclusion is precisely the inverse image of the original inclusion. -/
@[simp] theorem cmHarrisGeometricCoefficientShiftInclusion_app (k : ℕ) (r : ℕᵒᵖ) :
    (shiftInclusion k).app r = (geometricPullback).map ((originalInclusion k).app r) := rfl

/-- Each geometric reduction is precisely the inverse image of the original reduction. -/
@[simp] theorem cmHarrisGeometricCoefficientShiftReduction_app (k : ℕ) (r : ℕᵒᵖ) :
    (shiftReduction k).app r = (geometricPullback).map ((originalReduction k).app r) := rfl

/-- Exact inverse image preserves monicity of each original normalized inclusion. -/
instance cmHarrisGeometricCoefficientShiftInclusion_app_mono (k : ℕ) (r : ℕᵒᵖ) :
    Mono ((shiftInclusion k).app r) := by
  change Mono ((geometricPullback).map
    (originalInclusionLE (Nat.le_add_right r.unop k)))
  infer_instance

/-- The geometric finite-shift inclusion is a monomorphism of the sheaf diagrams. -/
instance cmHarrisGeometricCoefficientShiftInclusion_mono (k : ℕ) :
    Mono (shiftInclusion k) :=
  NatTrans.mono_of_mono_app _

/-- Inclusion followed by reduction is the original scalar power on the geometric tower. -/
@[reassoc (attr := simp)] theorem cmHarrisGeometricCoefficientShiftInclusion_reduction
    (k : ℕ) :
    shiftInclusion k ≫ shiftReduction k = powSMul m k system := by
  apply NatTrans.ext
  funext r
  change (geometricPullback).map ((originalInclusion k).app r) ≫
    (geometricPullback).map ((originalReduction k).app r) =
      powSMul m k ((geometricPullback).obj _)
  rw [← (geometricPullback).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisCoefficientShiftInclusion_reduction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k)
  change (originalInclusion k).app r ≫ (originalReduction k).app r =
    powSMul m k ((originalSystem).obj r) at heq
  rw [heq, map_powSMul]

/-- The reverse composite is the same scalar power on the geometric shifted tower. -/
@[reassoc (attr := simp)] theorem cmHarrisGeometricCoefficientShiftReduction_inclusion
    (k : ℕ) :
    shiftReduction k ≫ shiftInclusion k = powSMul m k (shifted k) := by
  apply NatTrans.ext
  funext r
  change (geometricPullback).map ((originalReduction k).app r) ≫
    (geometricPullback).map ((originalInclusion k).app r) =
      powSMul m k ((geometricPullback).obj ((originalShifted k).obj r))
  rw [← (geometricPullback).map_comp]
  have heq := congrArg (fun f => f.app r)
    (cmHarrisCoefficientShiftReduction_inclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k)
  change (originalReduction k).app r ≫ (originalInclusion k).app r =
    powSMul m k ((originalShifted k).obj r) at heq
  rw [heq, map_powSMul]

local notation "H" d => EtaleDerivedSections.cohomology X Rcoeff d
local notation "RH" => EtaleDerivedSections.homotopyFunctor X Rcoeff

local instance cmGeometricCohomology_additive (d : ℕ) : (H d).Additive :=
  Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive
    (EtaleDerivedSections.sections X Rcoeff) d

/-- Derived global sections of every geometric CM coefficient sheaf, with all reductions. -/
def cmHarrisGeometricCoefficientDerivedSystem :
    ℕᵒᵖ ⥤ HomotopyCategory (ModuleCat.{0} Rcoeff) (ComplexShape.up ℕ) :=
  system ⋙ RH

/-- Ordinary small-etale cohomology of the actual geometric CM coefficient system. -/
def cmHarrisGeometricCoefficientCohomologySystem (d : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{0} Rcoeff :=
  system ⋙ H d

local notation "cohomologySystem" => cmHarrisGeometricCoefficientCohomologySystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "derivedSystem" => cmHarrisGeometricCoefficientDerivedSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Cohomology transitions are the image of the actual geometric sheaf reductions. -/
@[simp] theorem cmHarrisGeometricCoefficientCohomologySystem_map (d : ℕ)
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (cohomologySystem d).map f = (H d).map ((system).map f) := rfl

/-- The coefficient tower in degree zero is naturally the geometric global-section tower. -/
def cmHarrisGeometricCoefficientCohomologyZeroIso :
    cohomologySystem 0 ≅ system ⋙ EtaleDerivedSections.sections X Rcoeff :=
  Functor.isoWhiskerLeft system (EtaleDerivedSections.cohomologyZeroIso X Rcoeff)

/-- The actual chosen injective-resolution complex represents each derived component. -/
def cmHarrisGeometricCoefficientDerivedSystemObjIso (r : ℕᵒᵖ) :
    (derivedSystem).obj r ≅
      (HomotopyCategory.quotient _ _).obj
        (EtaleDerivedSections.complex X Rcoeff ((system).obj r)) :=
  EtaleDerivedSections.complexIso X Rcoeff ((system).obj r)

/-- The resolution computes each actual coefficient cohomology module. -/
def cmHarrisGeometricCoefficientCohomologySystemObjIso (d : ℕ) (r : ℕᵒᵖ) :
    (cohomologySystem d).obj r ≅
      (EtaleDerivedSections.complex X Rcoeff ((system).obj r)).homology d :=
  EtaleDerivedSections.cohomologyIso X Rcoeff ((system).obj r) d

/-- Derived cohomology retains each finite-stage annihilating scalar. -/
theorem cmHarrisGeometricCoefficientCohomologySystem_powSMul_eq_zero (d r : ℕ) :
    powSMul m r ((cohomologySystem d).obj (op r)) = 0 := by
  change powSMul m r ((H d).obj ((system).obj (op r))) = 0
  rw [← map_powSMul, cmHarrisGeometricCoefficientSystem_powSMul_eq_zero, Functor.map_zero]

/-- Apply the cohomology functor to the geometric shifted coefficient tower. -/
def cmHarrisGeometricCoefficientCohomologyShiftedSystem (d k : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{0} Rcoeff := shifted k ⋙ H d

local notation "shiftedCohomology" => cmHarrisGeometricCoefficientCohomologyShiftedSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The finite-shift normalized inclusions induce actual cohomology maps. -/
def cmHarrisGeometricCoefficientCohomologyShiftInclusion (d k : ℕ) :
    cohomologySystem d ⟶ shiftedCohomology d k :=
  Functor.whiskerRight (shiftInclusion k) (H d)

/-- The geometric finite-shift reductions induce the reverse cohomology map. -/
def cmHarrisGeometricCoefficientCohomologyShiftReduction (d k : ℕ) :
    shiftedCohomology d k ⟶ cohomologySystem d :=
  Functor.whiskerRight (shiftReduction k) (H d)

local notation "cohomologyInclusion" => cmHarrisGeometricCoefficientCohomologyShiftInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "cohomologyReduction" => cmHarrisGeometricCoefficientCohomologyShiftReduction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The first cohomology composite is the prescribed scalar power on the geometric tower. -/
@[reassoc (attr := simp)] theorem cmHarrisGeometricCoefficientCohomologyShiftInclusion_reduction
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
    (cmHarrisGeometricCoefficientShiftInclusion_reduction D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k)
  change (shiftInclusion k).app r ≫ (shiftReduction k).app r =
    powSMul m k ((system).obj r) at heq
  rw [heq, map_powSMul]

/-- The opposite cohomology composite is the same scalar on the shifted tower. -/
@[reassoc (attr := simp)] theorem cmHarrisGeometricCoefficientCohomologyShiftReduction_inclusion
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
    (cmHarrisGeometricCoefficientShiftReduction_inclusion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k)
  change (shiftReduction k).app r ≫ (shiftInclusion k).app r =
    powSMul m k ((shifted k).obj r) at heq
  rw [heq, map_powSMul]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
