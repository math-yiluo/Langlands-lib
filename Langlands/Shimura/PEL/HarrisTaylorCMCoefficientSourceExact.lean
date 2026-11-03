import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientLocalExact
import Langlands.Shimura.Coefficients.VaryingCoverSourceChange

/-! # Compatible exact CM coefficient models on common source covers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Langlands.Sheaf
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

variable {k : ℕᵒᵖ} (a : k ⟶ i)

/-- Evaluate the independently descended kernel on any finer original cover. -/
def cmHarrisCoefficientSystemKernelTrivializationAlong :
    (localize k).obj kernelSheaf ≅
      (localize k).obj ((constant).obj (kernelAction).V) :=
  (associatedTrivializationAlongOfSplitting J ((covers).action i) ((covers).obj.map a)
    (etaleTorsorSectionSplitting X _ ((covers).action i) (coverProperty i) Rcoeff)).app
      (((constant).mapAction _).obj kernelAction)

local notation "kernelAlong" a => cmHarrisCoefficientSystemKernelTrivializationAlong
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f a

/-- Identity-source kernel evaluation recovers the existing original-cover model. -/
@[simp] theorem cmHarrisCoefficientSystemKernelTrivializationAlong_id :
    (kernelAlong (𝟙 i)) = kernelTrivialization := by
  apply Iso.ext
  change associatedEvaluationAlong J ((covers).action i) ((covers).obj.map (𝟙 i))
      (((constant).mapAction _).obj kernelAction) =
    associatedEvaluation J ((covers).action i) (((constant).mapAction _).obj kernelAction)
  rw [CategoryTheory.Functor.map_id]
  exact associatedEvaluationAlong_id J ((covers).action i)
    (((constant).mapAction _).obj kernelAction)

/-- The kernel-inclusion square holds on every common finer original cover. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelInclusion_evaluationAlong :
    (localize k).map kernelInclusion ≫ (along a).hom =
      (kernelAlong a).hom ≫
        (localize k).map ((constant).map (kernel.ι φ).hom) :=
  (associatedEvaluationAlongNat J ((covers).action i) ((covers).obj.map a)).naturality
    (((constant).mapAction _).map (kernel.ι φ))

/-- The ordinary linear-kernel model on any common finer original cover. -/
def cmHarrisCoefficientSystemKernelLinearTrivializationAlong :
    (localize k).obj kernelSheaf ≅
      (localize k).obj ((constant).obj
        (ModuleCat.of Rcoeff ((φ).hom.hom.ker))) :=
  (kernelAlong a) ≪≫ (localize k).mapIso ((constant).mapIso kernelModuleIso)

local notation "linearAlong" a => cmHarrisCoefficientSystemKernelLinearTrivializationAlong
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f a

/-- The ordinary kernel model at the identity is the existing fine-cover model. -/
@[simp] theorem cmHarrisCoefficientSystemKernelLinearTrivializationAlong_id :
    (linearAlong (𝟙 i)) =
      cmHarrisCoefficientSystemKernelLinearTrivialization D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid f := by
  apply Iso.ext
  change (kernelAlong (𝟙 i)).hom ≫
      (localize i).map ((constant).map (kernelModuleIso).hom) =
    (kernelTrivialization).hom ≫
      (localize i).map ((constant).map (kernelModuleIso).hom)
  rw [cmHarrisCoefficientSystemKernelTrivializationAlong_id]

/-- The evaluated kernel inclusion is the actual ordinary subtype on the common cover. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelInclusion_evaluationAlong_linear :
    (localize k).map kernelInclusion ≫ (along a).hom =
      (linearAlong a).hom ≫
        (localize k).map ((constant).map
          (ModuleCat.ofHom ((φ).hom.hom.ker.subtype))) := by
  dsimp only [cmHarrisCoefficientSystemKernelLinearTrivializationAlong, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    cmHarrisCoefficientTransitionKernelModuleIso_hom_subtype]
  exact cmHarrisCoefficientSystemKernelInclusion_evaluationAlong D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor q U
    ρ p m hm existence geometry hRigid f a

/-- All three terms of the actual reduction sequence on any common source cover. -/
def cmHarrisCoefficientReductionSequenceSourceIso :
    (sequence).map (localize k) ≅
      (cmHarrisCoefficientLinearReductionSequence D U ρ p m hm f).map
        ((constant) ⋙ localize k) :=
  ShortComplex.isoMk (linearAlong a) (along a) (along (a ≫ f))
    (cmHarrisCoefficientSystemKernelInclusion_evaluationAlong_linear D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid f a).symm
    (cmHarrisCoefficientSystem_map_evaluationAlong D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid a f).symm

local notation "sourceIso" a => cmHarrisCoefficientReductionSequenceSourceIso
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid f a

/-- The entire common-source model recovers the existing fine-cover sequence model. -/
@[simp] theorem cmHarrisCoefficientReductionSequenceSourceIso_id :
    (sourceIso (𝟙 i)) =
      cmHarrisCoefficientReductionSequenceLocalIso D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid f := by
  apply Iso.ext
  apply ShortComplex.hom_ext
  · exact congrArg Iso.hom
      (cmHarrisCoefficientSystemKernelLinearTrivializationAlong_id D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor q U
        ρ p m hm existence geometry hRigid f)
  · exact congrArg Iso.hom
      (cmHarrisCoefficientSystemTrivializationAlong_id D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid i)
  · change (along (𝟙 i ≫ f)).hom = (along f).hom
    rw [Category.id_comp]

variable {l : ℕᵒᵖ} (b : l ⟶ k)

local notation "restrict" => (J).overMapPullback (ModuleCat.{0} Rcoeff)
  ((covers).obj.map b)
local notation "sourceComparison" =>
  overPullbackMapIso J (ModuleCat.{0} Rcoeff) ((covers).obj.map b)

/-- Original stage evaluation is compatible with further source-cover refinement. -/
@[reassoc] theorem cmHarrisCoefficientSystemTrivializationAlong_sourceChange :
    (restrict).map (along a).hom ≫
        (sourceComparison).hom.app ((constant).obj ((coefficients).obj.obj i)) =
      (sourceComparison).hom.app ((system).obj i) ≫ (along (b ≫ a)).hom := by
  change (restrict).map
      (etaleAssociatedEvaluationAlong X covers coefficients i ((covers).obj.map a)) ≫
        (sourceComparison).hom.app ((constant).obj ((coefficients).obj.obj i)) =
      (sourceComparison).hom.app ((system).obj i) ≫
        etaleAssociatedEvaluationAlong X covers coefficients i ((covers).obj.map (b ≫ a))
  rw [Functor.map_comp]
  exact etaleAssociatedEvaluationAlong_sourceChange X covers coefficients i
    ((covers).obj.map b) ((covers).obj.map a)

/-- The independently descended kernel evaluation respects source-cover refinement. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelTrivializationAlong_sourceChange :
    (restrict).map (kernelAlong a).hom ≫
        (sourceComparison).hom.app ((constant).obj (kernelAction).V) =
      (sourceComparison).hom.app kernelSheaf ≫ (kernelAlong (b ≫ a)).hom := by
  change (restrict).map
      (associatedEvaluationAlong J ((covers).action i) ((covers).obj.map a)
        (((constant).mapAction _).obj kernelAction)) ≫
        (sourceComparison).hom.app ((constant).obj (kernelAction).V) =
      (sourceComparison).hom.app kernelSheaf ≫
        associatedEvaluationAlong J ((covers).action i) ((covers).obj.map (b ≫ a))
          (((constant).mapAction _).obj kernelAction)
  rw [Functor.map_comp]
  exact associatedEvaluationAlong_sourceChange J ((covers).action i)
    ((covers).obj.map b) ((covers).obj.map a)
    (((constant).mapAction _).obj kernelAction)

/-- The ordinary linear-kernel normalization also respects source-cover refinement. -/
@[reassoc] theorem cmHarrisCoefficientSystemKernelLinearTrivializationAlong_sourceChange :
    (restrict).map (linearAlong a).hom ≫
        (sourceComparison).hom.app
          ((constant).obj (ModuleCat.of Rcoeff ((φ).hom.hom.ker))) =
      (sourceComparison).hom.app kernelSheaf ≫ (linearAlong (b ≫ a)).hom := by
  change (restrict).map ((kernelAlong a).hom ≫
      (localize k).map ((constant).map (kernelModuleIso).hom)) ≫
        (sourceComparison).hom.app
          ((constant).obj (ModuleCat.of Rcoeff ((φ).hom.hom.ker))) =
      (sourceComparison).hom.app kernelSheaf ≫
        ((kernelAlong (b ≫ a)).hom ≫
          (localize l).map ((constant).map (kernelModuleIso).hom))
  rw [Functor.map_comp, Category.assoc]
  calc
    _ = (restrict).map (kernelAlong a).hom ≫
        ((sourceComparison).hom.app ((constant).obj (kernelAction).V) ≫
          (localize l).map ((constant).map (kernelModuleIso).hom)) :=
      congrArg (fun c => (restrict).map (kernelAlong a).hom ≫ c)
        ((sourceComparison).hom.naturality ((constant).map (kernelModuleIso).hom))
    _ = _ := by
      rw [← Category.assoc,
        cmHarrisCoefficientSystemKernelTrivializationAlong_sourceChange, Category.assoc]

/-- The complete actual reduction-sequence model commutes with further source changes. -/
theorem cmHarrisCoefficientReductionSequenceSourceIso_sourceChange :
    (restrict).mapShortComplex.map (sourceIso a).hom ≫
        ((cmHarrisCoefficientLinearReductionSequence D U ρ p m hm f).mapNatIso
          (Functor.isoWhiskerLeft (constant) sourceComparison)).hom =
      ((sequence).mapNatIso sourceComparison).hom ≫ (sourceIso (b ≫ a)).hom := by
  apply ShortComplex.hom_ext
  · exact cmHarrisCoefficientSystemKernelLinearTrivializationAlong_sourceChange
      D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid f a b
  · exact cmHarrisCoefficientSystemTrivializationAlong_sourceChange
      D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid a b
  · change (restrict).map (along (a ≫ f)).hom ≫
        (sourceComparison).hom.app ((constant).obj ((coefficients).obj.obj j)) =
      (sourceComparison).hom.app ((system).obj j) ≫ (along ((b ≫ a) ≫ f)).hom
    rw [Category.assoc b a f]
    exact cmHarrisCoefficientSystemTrivializationAlong_sourceChange
      D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U
      ρ p m hm existence geometry hRigid (a ≫ f) b

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
