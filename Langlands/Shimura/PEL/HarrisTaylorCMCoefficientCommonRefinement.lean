import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientRefinementCoherence

/-! # Common normal covers for original CM coefficient sheaves -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
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
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

variable (hRigid : CMGeometricCoarseRigidity D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor U.obj)

variable
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0) (k : ℕ)

local notation "X" => Functor.obj (schemes q) U
local notation "Vcoeff" => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "Rcoeff" => HarrisCoefficientReductionRing K p m k
local notation "Mcoeff" => cmHarrisCoefficientAction D ρ p U m hm k
local notation "J" => Scheme.smallEtaleTopology X

local notation "torsorAt" => cmHarrisRefinementTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "sheafAt" => cmHarrisRefinementCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "inclusionAt" => cmHarrisRefinementCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "isoAt" => cmHarrisCoefficientRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "coverAt" => cmHarrisCoefficientRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "trivializationAt" => cmHarrisRefinementCoefficientTrivialization D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
set_option quotPrecheck false in
local notation "constantModule" => (constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V

/-- The actual identity-Hecke intersection supplies a common small level. -/
def smallCMCommonLevel (V W₁ : SmallCMLevel D) : SmallCMLevel D :=
  smallCMHeckeLevel D V W₁ 1

omit [IsCMField F] [IsScalarTower E F A] [Module.Finite ℚ A] in
@[simp] theorem smallCMCommonLevel_subgroup (V W₁ : SmallCMLevel D) :
    (smallCMCommonLevel D V W₁).obj.subgroup = V.obj.subgroup ⊓ W₁.obj.subgroup := by
  ext g
  change (g ∈ V.obj.subgroup ∧
    (1 : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹ * g * (1⁻¹)⁻¹ ∈ W₁.obj.subgroup) ↔ _
  simp only [inv_one, one_mul, mul_one, Subgroup.mem_inf]

omit [IsCMField F] [IsScalarTower E F A] [Module.Finite ℚ A] in
theorem smallCMCommonLevel_le_left (V W₁ : SmallCMLevel D) :
    (smallCMCommonLevel D V W₁).obj.subgroup ≤ V.obj.subgroup := by
  rw [smallCMCommonLevel_subgroup]
  exact inf_le_left

omit [IsCMField F] [IsScalarTower E F A] [Module.Finite ℚ A] in
theorem smallCMCommonLevel_le_right (V W₁ : SmallCMLevel D) :
    (smallCMCommonLevel D V W₁).obj.subgroup ≤ W₁.obj.subgroup := by
  rw [smallCMCommonLevel_subgroup]
  exact inf_le_right

/-- The common intersection is normal in the same original coarse level. -/
instance smallCMCommonLevel_normal (V W₁ : SmallCMLevel D)
    [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    [(W₁.obj.subgroup.subgroupOf U.obj.subgroup).Normal] :
    ((smallCMCommonLevel D V W₁).obj.subgroup.subgroupOf U.obj.subgroup).Normal := by
  rw [smallCMCommonLevel_subgroup]
  change ((V.obj.subgroup.subgroupOf U.obj.subgroup) ⊓
    (W₁.obj.subgroup.subgroupOf U.obj.subgroup)).Normal
  infer_instance


variable (V W₁ : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  [(W₁.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (hV : V.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)
  (hW : W₁.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)

local notation "T" => smallCMCommonLevel D V W₁
local notation "hTV" => smallCMCommonLevel_le_left D V W₁
local notation "hTW" => smallCMCommonLevel_le_right D V W₁
set_option quotPrecheck false in
local notation "hT" => (smallCMCommonLevel_le_left D V W₁).trans hV
local notation "compareAt" => cmHarrisSuccessiveRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "successiveCover" => cmHarrisSuccessiveRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "successiveAction" => cmHarrisSuccessiveRefinementActionIso D U ρ p m hm k
local notation "aVT" => successiveCover V T hV hT hTV
local notation "aWT" => successiveCover W₁ T hW hT hTW
local notation "φVT" => smallCMResidualQuotientMap D U V T hTV
local notation "φWT" => smallCMResidualQuotientMap D U W₁ T hTW
set_option quotPrecheck false in
local notation "rVT" => etaleCrossCoverMap X φVT aVT (successiveAction V T hV hT hTV).hom
set_option quotPrecheck false in
local notation "rWT" => etaleCrossCoverMap X φWT aWT (successiveAction W₁ T hW hT hTW).hom

/-- Actual restriction from the first cover to the constructed common cover is invertible. -/
theorem cmHarrisCommonRefinementLeftMap_isIso : IsIso rVT := by
  rw [← cmHarrisSuccessiveRefinementIso_hom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V T hV hT hTV]
  infer_instance

/-- Actual restriction from the second cover to the constructed common cover is invertible. -/
theorem cmHarrisCommonRefinementRightMap_isIso : IsIso rWT := by
  rw [← cmHarrisSuccessiveRefinementIso_hom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k W₁ T hW hT hTW]
  infer_instance

/-- Compare unrelated normal covers by their actual cross-cover maps to the common intersection. -/
def cmHarrisCommonRefinementIso : sheafAt V hV ≅ sheafAt W₁ hW := by
  letI : IsIso rVT := cmHarrisCommonRefinementLeftMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV
  letI : IsIso rWT := cmHarrisCommonRefinementRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  exact asIso rVT ≪≫ (asIso rWT).symm

local notation "eCommon" => cmHarrisCommonRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW

/-- Restriction to the actual common cover normalizes the common-refinement comparison. -/
@[reassoc] theorem cmHarrisCommonRefinementIso_hom_comp :
    (eCommon).hom ≫ rWT = rVT := by
  have : IsIso rWT := cmHarrisCommonRefinementRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  change (rVT ≫ inv rWT) ≫ rWT = rVT
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Comparison via the common cover is the canonical independent-cover comparison. -/
theorem cmHarrisCommonRefinementIso_eq_successive :
    eCommon = compareAt V W₁ hV hW := by
  have : IsIso rWT := cmHarrisCommonRefinementRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  apply Iso.ext
  apply (cancel_mono rWT).1
  rw [cmHarrisCommonRefinementIso_hom_comp]
  rw [← cmHarrisSuccessiveRefinementIso_hom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k W₁ T hW hT hTW,
    ← cmHarrisSuccessiveRefinementIso_hom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V T hV hT hTV]
  exact (cmHarrisSuccessiveRefinementIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW T hT).symm

/-- The canonical independent-cover comparison agrees after actual restriction to the common cover. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_common_comp :
    (compareAt V W₁ hV hW).hom ≫ rWT = rVT := by
  rw [← cmHarrisCommonRefinementIso_eq_successive D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW]
  exact cmHarrisCommonRefinementIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

local notation "actionV" => cmHarrisResidualCoefficientAction D ρ p U V m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k V hV)
local notation "actionW" => cmHarrisResidualCoefficientAction D ρ p U W₁ m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k W₁ hW)

/-- Evaluation along either actual forgetting map agrees on the constructed common cover. -/
@[reassoc] theorem cmHarrisCommonRefinementIso_evaluation :
    ((J).overPullback (ModuleCat.{0} Rcoeff) (torsorAt T hT).val.V).map (eCommon).hom ≫
        associatedEvaluationAlong J (torsorAt W₁ hW).val (aWT).hom
          (((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
            (SmallCMResidualGroup D U W₁)).obj actionW) =
      associatedEvaluationAlong J (torsorAt V hV).val (aVT).hom
        (((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
          (SmallCMResidualGroup D U V)).obj actionV) := by
  rw [← cmHarrisSuccessiveRefinementIso_evaluation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k W₁ T hW hT hTW,
    ← cmHarrisSuccessiveRefinementIso_evaluation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V T hV hT hTV,
    ← Category.assoc, ← Functor.map_comp,
    cmHarrisCommonRefinementIso_eq_successive D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V W₁ hV hW,
    cmHarrisSuccessiveRefinementIso_hom_comp]


/-- The actual common-cover restriction equation uniquely characterizes the forward comparison. -/
theorem cmHarrisCommonRefinementIso_hom_unique
    (f : sheafAt V hV ⟶ sheafAt W₁ hW) (hf : f ≫ rWT = rVT) :
    f = (eCommon).hom := by
  have : IsIso rWT := cmHarrisCommonRefinementRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  apply (cancel_mono rWT).1
  exact hf.trans (cmHarrisCommonRefinementIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW).symm

/-- The canonical independent-cover comparison has the same common-cover evaluation normalization. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_common_evaluation :
    ((J).overPullback (ModuleCat.{0} Rcoeff) (torsorAt T hT).val.V).map
        (compareAt V W₁ hV hW).hom ≫
        associatedEvaluationAlong J (torsorAt W₁ hW).val (aWT).hom
          (((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
            (SmallCMResidualGroup D U W₁)).obj actionW) =
      associatedEvaluationAlong J (torsorAt V hV).val (aVT).hom
        (((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
          (SmallCMResidualGroup D U V)).obj actionV) := by
  rw [← cmHarrisCommonRefinementIso_eq_successive D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW]
  exact cmHarrisCommonRefinementIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
