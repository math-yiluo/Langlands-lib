import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSystem
import Langlands.Shimura.Coefficients.EtaleExact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Exact reduction sequences for original CM coefficient sheaves -/

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

variable {i j : ℕᵒᵖ} (f : i ⟶ j)
local notation "φ" => (coefficients).transition f
local notation "Fassoc" => etaleAssociatedFunctor (R := Rcoeff) X ((covers).action i)

/-- The actual kernel action of reduction on the full coefficient modules. -/
def cmHarrisCoefficientTransitionKernel :
    Action (ModuleCat.{0} Rcoeff) ((cmHarrisCoefficientGroups D ρ p U m hm).obj i) :=
  kernel φ

local notation "kernelAction" => cmHarrisCoefficientTransitionKernel D U ρ p m hm f

/-- The kernel carrier is the ordinary linear kernel of the original lattice reduction. -/
def cmHarrisCoefficientTransitionKernelModuleIso :
    (kernelAction).V ≅ ModuleCat.of Rcoeff (LinearMap.ker ((φ).hom.hom)) :=
  PreservesKernel.iso (Action.forget (ModuleCat.{0} Rcoeff) _) φ ≪≫
    ModuleCat.kernelIsoKer (φ).hom

/-- Every reduction kernel has a finite carrier. -/
theorem cmHarrisCoefficientTransitionKernel_finite : Finite (kernelAction).V := by
  have : Finite ((coefficients).action i).V :=
    cmHarrisCoefficientDiagram_finite D ρ p U m hm i
  have : Mono (kernel.ι φ).hom :=
    (Action.forget (ModuleCat.{0} Rcoeff) _).map_mono (kernel.ι φ)
  exact Finite.of_injective (kernel.ι φ).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- Surjectivity of the actual lattice reductions gives epimorphisms of actions. -/
instance cmHarrisCoefficientDiagram_transition_epi : Epi φ := by
  apply (Action.forget (ModuleCat.{0} Rcoeff) _).epi_of_epi_map
  exact (ModuleCat.epi_iff_surjective _).mpr
    (cmHarrisCoefficientDiagram_transition_surjective D ρ p U m hm f)

/-- Descend this actual finite kernel action on the original fine coefficient cover. -/
def cmHarrisCoefficientSystemKernelSheaf : Sheaf J (ModuleCat.{0} Rcoeff) :=
  (Fassoc).obj kernelAction

local notation "kernelSheaf" => cmHarrisCoefficientSystemKernelSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid f

/-- The kernel inclusion is the actual associated map of the module kernel inclusion. -/
def cmHarrisCoefficientSystemKernelInclusion : kernelSheaf ⟶ (system).obj i :=
  (Fassoc).map (kernel.ι φ)

local notation "kernelInclusion" => cmHarrisCoefficientSystemKernelInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f

/-- The actual kernel inclusion followed by the original sheaf transition is zero. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelInclusion_comp :
    kernelInclusion ≫ (system).map f = 0 := by
  change (Fassoc).map (kernel.ι φ) ≫
    ((Fassoc).map φ ≫ (etaleAssociatedComparisonIso X covers coverProperty f).inv.app
      coefficients) = 0
  rw [← Category.assoc, ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

/-- The reduction sequence uses independently descended module kernels and original transitions. -/
def cmHarrisCoefficientReductionSequence : ShortComplex (Sheaf J (ModuleCat.{0} Rcoeff)) :=
  ShortComplex.mk kernelInclusion ((system).map f)
    (cmHarrisCoefficientSystemKernelInclusion_comp D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid f)

local notation "sequence" => cmHarrisCoefficientReductionSequence D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid f

/-- Exact torsor association and the proved cover comparison identify the actual sequence. -/
def cmHarrisCoefficientReductionSequenceIso :
    (ShortComplex.kernelSequence φ).map Fassoc ≅ sequence :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((etaleAssociatedComparisonIso X covers coverProperty f).app coefficients).symm
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (Category.id_comp _)

/-- The original varying-cover coefficient reduction sequence is short exact. -/
theorem cmHarrisCoefficientReductionSequence_shortExact : (sequence).ShortExact := by
  have := etaleAssociatedFunctorPreservesFiniteLimits (R := Rcoeff) X ((covers).action i)
    (coverProperty i)
  have := etaleAssociatedFunctorPreservesFiniteColimits (R := Rcoeff) X ((covers).action i)
    (coverProperty i)
  have hs : (ShortComplex.kernelSequence φ).ShortExact := {
    exact := ShortComplex.kernelSequence_exact φ
    epi_g := cmHarrisCoefficientDiagram_transition_epi D U ρ p m hm f
  }
  exact ShortComplex.shortExact_of_iso
    (cmHarrisCoefficientReductionSequenceIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f)
    (hs.map_of_exact Fassoc)

/-- All original coefficient-system transitions are epimorphisms of sheaves. -/
instance cmHarrisCoefficientSystem_map_epi : Epi ((system).map f) :=
  (cmHarrisCoefficientReductionSequence_shortExact D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f).epi_g

/-- The descended kernel includes monomorphically into the original coefficient sheaf. -/
instance cmHarrisCoefficientSystemKernelInclusion_mono : Mono kernelInclusion :=
  (cmHarrisCoefficientReductionSequence_shortExact D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f).mono_f

/-- The independently descended module kernel is the kernel of the actual transition. -/
def cmHarrisCoefficientSystemKernelIso : kernelSheaf ≅ kernel ((system).map f) :=
  IsLimit.conePointUniqueUpToIso
    (cmHarrisCoefficientReductionSequence_shortExact D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid f).fIsKernel
    (limit.isLimit _)

/-- This comparison identifies the actual inclusion, rather than only the kernel objects. -/
@[reassoc (attr := simp)] theorem cmHarrisCoefficientSystemKernelIso_hom_ι :
    (cmHarrisCoefficientSystemKernelIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid f).hom ≫
      kernel.ι ((system).map f) = kernelInclusion :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The kernel sheaf has its actual finite constant model on the original fine cover. -/
def cmHarrisCoefficientSystemKernelTrivialization :
    ((J).overPullback (ModuleCat.{0} Rcoeff) ((covers).obj.obj i)).obj kernelSheaf ≅
      ((J).overPullback (ModuleCat.{0} Rcoeff) ((covers).obj.obj i)).obj
        ((constantSheaf J (ModuleCat.{0} Rcoeff)).obj (kernelAction).V) :=
  (constantAssociatedTrivializationOfSplitting J ((covers).action i)
    (etaleTorsorSectionSplitting X _ ((covers).action i) (coverProperty i) Rcoeff)).app kernelAction

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
