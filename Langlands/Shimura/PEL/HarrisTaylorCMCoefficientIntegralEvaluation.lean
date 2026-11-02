import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientIntegralCoherence
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientRefinementEvaluation

/-! # Integral evaluation along original CM normal coefficient refinements -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

local notation "R" => HarrisCoefficientIntegers K p
local notation "quotientMap" => Ideal.Quotient.mk (harrisCoefficientScalarIdeal K p m ^ k)
local notation "restriction" => sheafCompose J (ModuleCat.restrictScalars.{0} quotientMap)
local notation "integralAction" => (cmHarrisCoefficientDiagram D ρ p U m hm).action (Opposite.op k)
local notation "torsorAt" => cmHarrisRefinementTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "sheafAt" => cmHarrisRefinementIntegralSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "inclusionAt" => cmHarrisRefinementIntegralInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "isoAt" => cmHarrisRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "coverAt" => cmHarrisCoefficientRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "successiveCover" => cmHarrisSuccessiveRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "fineActionAt" => cmHarrisRefinementIntegralAction D U ρ p m hm k
local notation "constantModule" => (constantSheaf J (ModuleCat.{0} R)).obj (integralAction).V
local notation "systemInclusion" => cmHarrisCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid (Opposite.op k)

variable (V W₁ : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  [(W₁.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (hV : V.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)
  (hW : W₁.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)
  (hWV : W₁.obj.subgroup ≤ V.obj.subgroup)

local notation "aVW" => successiveCover V W₁ hV hW hWV
local notation "constantActionV" =>
  ((constantSheaf J (ModuleCat.{0} R)).mapAction
    (SmallCMResidualGroup D U V)).obj (fineActionAt V hV)
local notation "localize" => (J).overPullback (ModuleCat.{0} R) (torsorAt W₁ hW).val.V
local notation "compareAt" => cmHarrisSuccessiveRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "eVW" => compareAt V W₁ hV hW
local notation "trivializationAt" => cmHarrisRefinementIntegralTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k

/-- Independently evaluate integral invariants along the actual intermediate forgetting map. -/
def cmHarrisSuccessiveIntegralTrivializationAlong :
    (localize).obj (sheafAt V hV) ≅ (localize).obj constantModule :=
  (associatedTrivializationAlongOfSplitting J (torsorAt V hV).val (aVW).hom
    (etaleTorsorSectionSplitting X _ (torsorAt V hV).val
      (torsorAt V hV).property R)).app constantActionV

local notation "alongAt" => cmHarrisSuccessiveIntegralTrivializationAlong D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k
local notation "alongVW" => alongAt V W₁ hV hW hWV

/-- The independently constructed forward map is actual invariant graph evaluation. -/
theorem cmHarrisSuccessiveIntegralTrivializationAlong_hom :
    (alongVW).hom =
      associatedEvaluationAlong J (torsorAt V hV).val (aVW).hom constantActionV := rfl

/-- Integral comparison preserves evaluation along the actual nested forgetting map. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_evaluation :
    (localize).map (eVW).hom ≫ (trivializationAt W₁ hW).hom = (alongVW).hom := by
  change (localize).map (eVW).hom ≫
      ((localize).map (inclusionAt W₁ hW) ≫
        productEvaluation J (torsorAt W₁ hW).val constantModule) =
    (localize).map (inclusionAt V hV) ≫
      productEvaluationAlong J (aVW).hom constantModule
  rw [← Category.assoc, ← Functor.map_comp,
    cmHarrisSuccessiveRefinementIntegralIso_hom_inclusion, Functor.map_comp,
    Category.assoc, coverPullback_productEvaluation]

/-- Both independent nested integral evaluation isomorphisms agree, including their inverses. -/
theorem cmHarrisSuccessiveRefinementIntegralIso_trivialization :
    (localize).mapIso eVW ≪≫ trivializationAt W₁ hW = alongVW := by
  apply Iso.ext
  exact cmHarrisSuccessiveRefinementIntegralIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV

local notation "scalarAt" => cmHarrisRefinementSheafRestrictIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "quotientSheafAt" => cmHarrisRefinementCoefficientSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "quotientInclusionAt" => cmHarrisRefinementCoefficientInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "quotientActionV" => cmHarrisResidualCoefficientAction D ρ p U V m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k V hV)
local notation "constantQuotientActionV" =>
  ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U V)).obj quotientActionV
local notation "localRestrict" => sheafCompose ((J).over (torsorAt W₁ hW).val.V)
  (ModuleCat.restrictScalars.{0} quotientMap)
local notation "constantComparison" =>
  (constantRestrictScalarsIso J quotientMap).app (Mcoeff).V

/-- Independently evaluate quotient invariants along forgetting and restrict their scalars. -/
def cmHarrisSuccessiveRestrictedTrivializationAlong :
    (localize).obj ((restriction).obj (quotientSheafAt V hV)) ≅
      (localize).obj constantModule :=
  (localRestrict).mapIso
    ((associatedTrivializationAlongOfSplitting J (torsorAt V hV).val (aVW).hom
      (etaleTorsorSectionSplitting X _ (torsorAt V hV).val
        (torsorAt V hV).property Rcoeff)).app constantQuotientActionV) ≪≫
    (localize).mapIso constantComparison

local notation "restrictedAlongAt" => cmHarrisSuccessiveRestrictedTrivializationAlong D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k
local notation "restrictedAlongVW" => restrictedAlongAt V W₁ hV hW hWV

/-- Scalar compatibility holds for evaluation along the actual intermediate cover map. -/
@[reassoc] theorem cmHarrisSuccessiveSheafRestrictIso_evaluationAlong :
    (localize).map (scalarAt V hV).hom ≫ (alongVW).hom =
      (restrictedAlongVW).hom := by
  let loc := localize
  let c := (constantComparison).hom
  let F := (restriction).obj
    ((constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V)
  let F' := constantModule
  let b := (restriction).map (quotientInclusionAt V hV)
  have hi := cmHarrisRefinementSheafRestrictIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hi' := congrArg (fun f => loc.map f) hi
  have hi'' := ((loc.map_comp _ _).symm.trans hi').trans (loc.map_comp _ _)
  have hn := productEvaluationAlong_natural J (aVW).hom c
  change loc.map (scalarAt V hV).hom ≫
      (loc.map (inclusionAt V hV) ≫ productEvaluationAlong J (aVW).hom F') = _
  calc
    _ = (loc.map (scalarAt V hV).hom ≫ loc.map (inclusionAt V hV)) ≫
        productEvaluationAlong J (aVW).hom F' := (Category.assoc _ _ _).symm
    _ = (loc.map b ≫ loc.map ((productSheaf J (torsorAt V hV).val.V).map c)) ≫
        productEvaluationAlong J (aVW).hom F' :=
      congrArg (fun f => f ≫ productEvaluationAlong J (aVW).hom F') hi''
    _ = loc.map b ≫ (loc.map ((productSheaf J (torsorAt V hV).val.V).map c) ≫
        productEvaluationAlong J (aVW).hom F') := Category.assoc _ _ _
    _ = loc.map b ≫ (productEvaluationAlong J (aVW).hom F ≫ loc.map c) :=
      congrArg (fun f => loc.map b ≫ f) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- The full scalar-compatible isomorphisms agree along actual intermediate forgetting. -/
theorem cmHarrisSuccessiveSheafRestrictIso_trivializationAlong :
    (localize).mapIso (scalarAt V hV) ≪≫ alongVW = restrictedAlongVW := by
  apply Iso.ext
  exact cmHarrisSuccessiveSheafRestrictIso_evaluationAlong D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV

local notation "quotientCompareAt" => cmHarrisSuccessiveRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "restrictedTrivializationAt" => cmHarrisRefinementRestrictedTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k

/-- Nested coefficient comparison and scalar restriction agree after canonical evaluation. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementScalar_evaluation :
    (localize).map ((restriction).map (quotientCompareAt V W₁ hV hW).hom) ≫
        (restrictedTrivializationAt W₁ hW).hom =
      (localize).map (scalarAt V hV).hom ≫ (alongVW).hom := by
  have hFine := cmHarrisRefinementSheafRestrictIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k W₁ hW
  have hSquare := cmHarrisSuccessiveRefinementScalar_square D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  have hIntegral := cmHarrisSuccessiveRefinementIntegralIso_evaluation D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV
  have hMapped :
      (localize).map ((restriction).map (quotientCompareAt V W₁ hV hW).hom) ≫
          (localize).map (scalarAt W₁ hW).hom =
        (localize).map (scalarAt V hV).hom ≫ (localize).map (eVW).hom :=
    ((localize).map_comp _ _).symm.trans
      ((congrArg (fun f => (localize).map f) hSquare).trans
        ((localize).map_comp _ _))
  calc
    _ = (localize).map ((restriction).map (quotientCompareAt V W₁ hV hW).hom) ≫
        ((localize).map (scalarAt W₁ hW).hom ≫
          (trivializationAt W₁ hW).hom) :=
      congrArg
        (fun f => (localize).map ((restriction).map (quotientCompareAt V W₁ hV hW).hom) ≫ f)
        hFine.symm
    _ = ((localize).map ((restriction).map (quotientCompareAt V W₁ hV hW).hom) ≫
        (localize).map (scalarAt W₁ hW).hom) ≫
          (trivializationAt W₁ hW).hom := (Category.assoc _ _ _).symm
    _ = ((localize).map (scalarAt V hV).hom ≫ (localize).map (eVW).hom) ≫
        (trivializationAt W₁ hW).hom :=
      congrArg (fun f => f ≫ (trivializationAt W₁ hW).hom) hMapped
    _ = (localize).map (scalarAt V hV).hom ≫
        ((localize).map (eVW).hom ≫ (trivializationAt W₁ hW).hom) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun f => (localize).map (scalarAt V hV).hom ≫ f) hIntegral

/-- The complete scalar-compatible nested evaluation isomorphisms coincide. -/
theorem cmHarrisSuccessiveRefinementScalar_trivialization :
    (localize).mapIso ((restriction).mapIso (quotientCompareAt V W₁ hV hW)) ≪≫
        restrictedTrivializationAt W₁ hW =
      (localize).mapIso (scalarAt V hV) ≪≫ alongVW := by
  apply Iso.ext
  exact cmHarrisSuccessiveRefinementScalar_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV

local notation "T" => smallCMCommonLevel D V W₁
local notation "hTV" => smallCMCommonLevel_le_left D V W₁
local notation "hTW" => smallCMCommonLevel_le_right D V W₁
set_option quotPrecheck false in
local notation "hT" => (smallCMCommonLevel_le_left D V W₁).trans hV
local notation "localizeT" => (J).overPullback (ModuleCat.{0} R) (torsorAt T hT).val.V
local notation "alongVT" => alongAt V T hV hT hTV
local notation "alongWT" => alongAt W₁ T hW hT hTW
local notation "restrictedAlongVT" => restrictedAlongAt V T hV hT hTV
local notation "restrictedAlongWT" => restrictedAlongAt W₁ T hW hT hTW
local notation "eCommon" => cmHarrisCommonRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW
local notation "quotientCommon" => cmHarrisCommonRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW

/-- Evaluation along both actual common-cover maps agrees under integral comparison. -/
@[reassoc] theorem cmHarrisCommonRefinementIntegralIso_evaluation :
    (localizeT).map (eCommon).hom ≫ (alongWT).hom = (alongVT).hom := by
  rw [← cmHarrisSuccessiveRefinementIntegralIso_evaluation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k W₁ T hW hT hTW,
    ← cmHarrisSuccessiveRefinementIntegralIso_evaluation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V T hV hT hTV,
    ← Category.assoc, ← Functor.map_comp,
    cmHarrisCommonRefinementIntegralIso_eq_successive D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V W₁ hV hW,
    cmHarrisSuccessiveRefinementIntegralIso_hom_comp]

/-- Both independently constructed common-cover integral evaluation isomorphisms agree. -/
theorem cmHarrisCommonRefinementIntegralIso_trivialization :
    (localizeT).mapIso eCommon ≪≫ alongWT = alongVT := by
  apply Iso.ext
  exact cmHarrisCommonRefinementIntegralIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

/-- The canonical independent-cover comparison has the same actual common-cover evaluation. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_common_evaluation :
    (localizeT).map (eVW).hom ≫ (alongWT).hom = (alongVT).hom := by
  rw [← cmHarrisCommonRefinementIntegralIso_eq_successive D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW]
  exact cmHarrisCommonRefinementIntegralIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

/-- Common-cover comparison and scalar restriction agree after evaluation along forgetting. -/
@[reassoc] theorem cmHarrisCommonRefinementScalar_evaluation :
    (localizeT).map ((restriction).map (quotientCommon).hom) ≫
        (restrictedAlongWT).hom =
      (localizeT).map (scalarAt V hV).hom ≫ (alongVT).hom := by
  have hScalarW := cmHarrisSuccessiveSheafRestrictIso_evaluationAlong D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k W₁ T hW hT hTW
  have hSquare := cmHarrisCommonRefinementScalar_square D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  have hIntegral := cmHarrisCommonRefinementIntegralIso_evaluation D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  have hMapped :
      (localizeT).map ((restriction).map (quotientCommon).hom) ≫
          (localizeT).map (scalarAt W₁ hW).hom =
        (localizeT).map (scalarAt V hV).hom ≫ (localizeT).map (eCommon).hom :=
    ((localizeT).map_comp _ _).symm.trans
      ((congrArg (fun f => (localizeT).map f) hSquare).trans
        ((localizeT).map_comp _ _))
  calc
    _ = (localizeT).map ((restriction).map (quotientCommon).hom) ≫
        ((localizeT).map (scalarAt W₁ hW).hom ≫ (alongWT).hom) :=
      congrArg (fun f => (localizeT).map ((restriction).map (quotientCommon).hom) ≫ f)
        hScalarW.symm
    _ = ((localizeT).map ((restriction).map (quotientCommon).hom) ≫
        (localizeT).map (scalarAt W₁ hW).hom) ≫ (alongWT).hom :=
      (Category.assoc _ _ _).symm
    _ = ((localizeT).map (scalarAt V hV).hom ≫
        (localizeT).map (eCommon).hom) ≫ (alongWT).hom :=
      congrArg (fun f => f ≫ (alongWT).hom) hMapped
    _ = (localizeT).map (scalarAt V hV).hom ≫
        ((localizeT).map (eCommon).hom ≫ (alongWT).hom) := Category.assoc _ _ _
    _ = _ := congrArg (fun f => (localizeT).map (scalarAt V hV).hom ≫ f) hIntegral

/-- The full scalar-compatible evaluation isomorphisms agree on the actual common cover. -/
theorem cmHarrisCommonRefinementScalar_trivialization :
    (localizeT).mapIso ((restriction).mapIso quotientCommon) ≪≫ restrictedAlongWT =
      (localizeT).mapIso (scalarAt V hV) ≪≫ alongVT := by
  apply Iso.ext
  exact cmHarrisCommonRefinementScalar_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

/-- Independently scalar-restricted quotient evaluations agree after common-cover comparison. -/
@[reassoc] theorem cmHarrisCommonRefinementRestricted_evaluation :
    (localizeT).map ((restriction).map (quotientCommon).hom) ≫
        (restrictedAlongWT).hom = (restrictedAlongVT).hom :=
  (cmHarrisCommonRefinementScalar_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW).trans
      (cmHarrisSuccessiveSheafRestrictIso_evaluationAlong D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U existence geometry
        hRigid ρ p m hm k V T hV hT hTV)

/-- Common-cover comparison preserves the full independently restricted evaluation isomorphism. -/
theorem cmHarrisCommonRefinementRestricted_trivialization :
    (localizeT).mapIso ((restriction).mapIso quotientCommon) ≪≫ restrictedAlongWT =
      restrictedAlongVT := by
  apply Iso.ext
  exact cmHarrisCommonRefinementRestricted_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
