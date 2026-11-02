import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientExact
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientLocalReduction
import Langlands.Sheaf.SourceSliceExact

/-! # Local linear models for exact original CM coefficient reductions -/

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
open Langlands.Shimura.Coefficients

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
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "torsor" k => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

local notation "localize" k =>
  (J).overPullback (ModuleCat.{0} Rcoeff) ((covers).obj.obj k)
local notation "constant" => constantSheaf J (ModuleCat.{0} Rcoeff)
local notation "trivialization" => cmHarrisCoefficientSystemTrivialization D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "along" => cmHarrisCoefficientSystemTrivializationAlong D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

variable {i j : ℕᵒᵖ} (f : i ⟶ j)
local notation "φ" => (coefficients).transition f
local notation "kernelAction" => cmHarrisCoefficientTransitionKernel D U ρ p m hm f
local notation "kernelModuleIso" =>
  cmHarrisCoefficientTransitionKernelModuleIso D U ρ p m hm f
local notation "kernelSheaf" => cmHarrisCoefficientSystemKernelSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid f
local notation "kernelInclusion" => cmHarrisCoefficientSystemKernelInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f
local notation "kernelTrivialization" => cmHarrisCoefficientSystemKernelTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f
local notation "sequence" => cmHarrisCoefficientReductionSequence D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid f

/-- The action-kernel comparison preserves the actual ordinary linear-kernel inclusion. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientTransitionKernelModuleIso_hom_subtype :
    (kernelModuleIso).hom ≫ ModuleCat.ofHom ((φ).hom.hom.ker.subtype) =
      (kernel.ι φ).hom := by
  dsimp [cmHarrisCoefficientTransitionKernelModuleIso]
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι φ (Action.forget (ModuleCat.{0} Rcoeff) _)

/-- The independently descended inclusion evaluates to the original kernel inclusion. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelInclusion_evaluation :
    (localize i).map kernelInclusion ≫ (trivialization i).hom =
      (kernelTrivialization).hom ≫
        (localize i).map ((constant).map (kernel.ι φ).hom) := by
  exact (constantAssociatedTrivializationOfSplitting J ((covers).action i)
    (etaleTorsorSectionSplitting X _ ((covers).action i) (coverProperty i) Rcoeff)).hom.naturality
      (kernel.ι φ)

/-- The finite descended kernel has its canonical ordinary linear-kernel model. -/
def cmHarrisCoefficientSystemKernelLinearTrivialization :
    (localize i).obj kernelSheaf ≅
      (localize i).obj ((constant).obj
        (ModuleCat.of Rcoeff ((φ).hom.hom.ker))) :=
  kernelTrivialization ≪≫ (localize i).mapIso ((constant).mapIso kernelModuleIso)

local notation "linearTrivialization" => cmHarrisCoefficientSystemKernelLinearTrivialization
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f

/-- In these coordinates the descended inclusion is the actual linear subtype map. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelInclusion_evaluation_linear :
    (localize i).map kernelInclusion ≫ (trivialization i).hom =
      (linearTrivialization).hom ≫
        (localize i).map ((constant).map
          (ModuleCat.ofHom ((φ).hom.hom.ker.subtype))) := by
  dsimp only [cmHarrisCoefficientSystemKernelLinearTrivialization, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    cmHarrisCoefficientTransitionKernelModuleIso_hom_subtype]
  exact cmHarrisCoefficientSystemKernelInclusion_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f

/-- The ordinary linear-kernel sequence of this actual full-lattice reduction. -/
def cmHarrisCoefficientLinearReductionSequence : ShortComplex (ModuleCat.{0} Rcoeff) :=
  ShortComplex.mk (ModuleCat.ofHom ((φ).hom.hom.ker.subtype)) (φ).hom (by
    ext x
    exact x.property)

/-- All three original local models identify the entire actual reduction sequence. -/
def cmHarrisCoefficientReductionSequenceLocalIso :
    (sequence).map (localize i) ≅
      (cmHarrisCoefficientLinearReductionSequence D U ρ p m hm f).map
        ((constant) ⋙ localize i) :=
  ShortComplex.isoMk linearTrivialization (trivialization i) (along f)
    (cmHarrisCoefficientSystemKernelInclusion_evaluation_linear D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid f).symm
    (cmHarrisCoefficientSystem_map_evaluation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid f).symm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
