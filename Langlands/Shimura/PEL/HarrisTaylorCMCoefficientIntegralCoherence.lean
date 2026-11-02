import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCommonRefinement
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientRefinementScalars

/-! # Integral coherence for original CM normal coefficient covers -/

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

local notation "φVW" => smallCMResidualQuotientMap D U V W₁ hWV
local notation "actionV" => fineActionAt V hV
local notation "actionW" => fineActionAt W₁ hW
local notation "aVW" => successiveCover V W₁ hV hW hWV

/-- Successive original residual actions remain identical on their integral coefficient module. -/
def cmHarrisSuccessiveRefinementIntegralActionIso :
    (Action.res (ModuleCat.{0} R) φVW).obj actionV ≅ actionW :=
  Action.mkIso (Iso.refl _) (by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (cmHarrisTorsionSystem D ρ p U m |>.obj (Opposite.op k)).ρ g ≫ 𝟙 _ =
        𝟙 _ ≫ (cmHarrisTorsionSystem D ρ p U m |>.obj (Opposite.op k)).ρ g
      simp only [Category.comp_id, Category.id_comp])

@[simp] theorem cmHarrisSuccessiveRefinementIntegralActionIso_hom_hom :
    (cmHarrisSuccessiveRefinementIntegralActionIso D U ρ p m hm k V W₁ hV hW hWV).hom.hom =
      𝟙 _ := rfl

@[simp] theorem cmHarrisSuccessiveRefinementIntegralActionIso_inv_hom :
    (cmHarrisSuccessiveRefinementIntegralActionIso D U ρ p m hm k V W₁ hV hW hWV).inv.hom =
      𝟙 _ := rfl

local notation "cVW" => cmHarrisSuccessiveRefinementIntegralActionIso D U ρ p m hm k
  V W₁ hV hW hWV

/-- Integral inverse comparison is normalized by actual original-cover section restriction. -/
@[reassoc] theorem cmHarrisRefinementIntegralIso_inv_inclusion :
    (isoAt V hV).inv ≫ systemInclusion ≫
      coverPullback J (coverAt V hV).hom constantModule = inclusionAt V hV := by
  rw [← cmHarrisRefinementIntegralIso_hom_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V hV]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Compare two independently constructed fine-cover sheaves through their canonical comparisons. -/
def cmHarrisSuccessiveRefinementIntegralIso : sheafAt V hV ≅ sheafAt W₁ hW :=
  (isoAt V hV).symm ≪≫ isoAt W₁ hW

local notation "eVW" => cmHarrisSuccessiveRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW

/-- The comparison restricts cover sections along the original intermediate forgetting map. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_hom_inclusion :
    (eVW).hom ≫ inclusionAt W₁ hW =
      inclusionAt V hV ≫ coverPullback J (aVW).hom constantModule := by
  change ((isoAt V hV).inv ≫ (isoAt W₁ hW).hom) ≫ inclusionAt W₁ hW = _
  rw [Category.assoc, cmHarrisRefinementIntegralIso_hom_inclusion,
    ← cmHarrisSuccessiveRefinementCover_triangle D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V W₁ hV hW hWV,
    coverPullback_comp]
  simpa only [Category.assoc] using
    cmHarrisRefinementIntegralIso_inv_inclusion_assoc D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V hV (coverPullback J (aVW).hom constantModule)

/-- The forward comparison is exactly the cross-cover map for actual forgetting and identity coefficients. -/
theorem cmHarrisSuccessiveRefinementIntegralIso_hom :
    (eVW).hom = etaleCrossCoverMap X φVW aVW (cVW).hom := by
  let c := ((constantSheaf J (ModuleCat.{0} R)).mapAction
    (SmallCMResidualGroup D U W₁)).map (cVW).hom
  have hc : c.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} R)).map (𝟙 (integralAction).V) = _
    exact (constantSheaf J (ModuleCat.{0} R)).map_id _
  have he := crossCoverMap_inclusion («R» := R) J φVW aVW
    (F := ((constantSheaf J (ModuleCat.{0} R)).mapAction
      (SmallCMResidualGroup D U V)).obj actionV)
    (E := ((constantSheaf J (ModuleCat.{0} R)).mapAction
      (SmallCMResidualGroup D U W₁)).obj actionW) c
  have hid : (productSheaf J (torsorAt W₁ hW).val.V).map (𝟙 constantModule) = 𝟙 _ :=
    (productSheaf J (torsorAt W₁ hW).val.V).map_id constantModule
  erw [hc, hid] at he
  have he' := he.trans (congrArg (fun b =>
    inclusionAt V hV ≫ b) (Category.comp_id
      (coverPullback J (aVW).hom constantModule)))
  apply Langlands.Shimura.Coefficients.hom_ext J (torsorAt W₁ hW).val
  exact (cmHarrisSuccessiveRefinementIntegralIso_hom_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV).trans he'.symm

/-- The inverse is normalized by restriction along the same intermediate forgetting map. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_inv_inclusion :
    (eVW).inv ≫ inclusionAt V hV ≫ coverPullback J (aVW).hom constantModule =
      inclusionAt W₁ hW := by
  rw [← cmHarrisSuccessiveRefinementIntegralIso_hom_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Comparing through any intermediate normal cover gives the original comparison. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_triangle :
    (isoAt V hV).hom ≫ (eVW).hom = (isoAt W₁ hW).hom := by
  change (isoAt V hV).hom ≫ ((isoAt V hV).inv ≫ (isoAt W₁ hW).hom) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- A level compared with itself has the identity coefficient comparison. -/
@[simp] theorem cmHarrisSuccessiveRefinementIntegralIso_refl :
    cmHarrisSuccessiveRefinementIntegralIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V V hV hV = Iso.refl (sheafAt V hV) := by
  apply Iso.ext
  exact (isoAt V hV).inv_hom_id

variable (V₂ : SmallCMLevel D)
  [(V₂.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (h₂ : V₂.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)
  (h₂W : V₂.obj.subgroup ≤ W₁.obj.subgroup)

local notation "aW₂" => cmHarrisSuccessiveRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k W₁ V₂ hW h₂ h₂W
local notation "aV₂" => cmHarrisSuccessiveRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V V₂ hV h₂ (h₂W.trans hWV)
local notation "eW₂" => cmHarrisSuccessiveRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k W₁ V₂ hW h₂
local notation "eV₂" => cmHarrisSuccessiveRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V V₂ hV h₂

/-- Successive comparisons of independent normal-cover sheaves agree with direct comparison. -/
theorem cmHarrisSuccessiveRefinementIntegralIso_comp :
    eVW ≪≫ eW₂ = eV₂ := by
  apply Iso.ext
  change ((isoAt V hV).inv ≫ (isoAt W₁ hW).hom) ≫
    ((isoAt W₁ hW).inv ≫ (isoAt V₂ h₂).hom) =
    (isoAt V hV).inv ≫ (isoAt V₂ h₂).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The forward module-sheaf maps satisfy the same strict composition equation. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_hom_comp :
    (eVW).hom ≫ (eW₂).hom = (eV₂).hom :=
  congrArg Iso.hom (cmHarrisSuccessiveRefinementIntegralIso_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW V₂ h₂)

local notation "cW₂" => cmHarrisSuccessiveRefinementIntegralActionIso D U ρ p m hm k
  W₁ V₂ hW h₂ h₂W
local notation "cV₂" => cmHarrisSuccessiveRefinementIntegralActionIso D U ρ p m hm k
  V V₂ hV h₂ (h₂W.trans hWV)

/-- The actual cross-cover maps for successive original refinements compose to direct forgetting. -/
@[reassoc] theorem cmHarrisSuccessiveIntegralCrossCoverMap_comp :
    etaleCrossCoverMap X φVW aVW (cVW).hom ≫
      etaleCrossCoverMap X (smallCMResidualQuotientMap D U W₁ V₂ h₂W) aW₂ (cW₂).hom =
    etaleCrossCoverMap X (smallCMResidualQuotientMap D U V V₂ (h₂W.trans hWV))
      aV₂ (cV₂).hom := by
  rw [← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V W₁ hV hW hWV,
    ← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k W₁ V₂ hW h₂ h₂W,
    ← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V V₂ hV h₂ (h₂W.trans hWV)]
  exact cmHarrisSuccessiveRefinementIntegralIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW V₂ h₂


local notation "quotientIsoAt" => cmHarrisCoefficientRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "quotientCompareAt" => cmHarrisSuccessiveRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "scalarAt" => cmHarrisRefinementSheafRestrictIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "coarseScalarIso" => cmHarrisCoefficientSheafRestrictIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k

/-- Comparison of any two normal coefficient covers commutes with integral scalar restriction. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementScalar_square :
    (restriction).map (quotientCompareAt V W₁ hV hW).hom ≫ (scalarAt W₁ hW).hom =
      (scalarAt V hV).hom ≫ (eVW).hom := by
  have hScalarV := cmHarrisRefinementScalar_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hScalarW := cmHarrisRefinementScalar_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k W₁ hW
  have hQuotient := cmHarrisSuccessiveRefinementIso_triangle D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  have hIntegral := cmHarrisSuccessiveRefinementIntegralIso_triangle D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  apply (cancel_epi ((restriction).map (quotientIsoAt V hV).hom)).1
  calc
    (restriction).map (quotientIsoAt V hV).hom ≫
        ((restriction).map (quotientCompareAt V W₁ hV hW).hom ≫ (scalarAt W₁ hW).hom) =
      (restriction).map ((quotientIsoAt V hV).hom ≫
        (quotientCompareAt V W₁ hV hW).hom) ≫ (scalarAt W₁ hW).hom := by
          rw [Functor.map_comp, Category.assoc]
    _ = (restriction).map (quotientIsoAt W₁ hW).hom ≫ (scalarAt W₁ hW).hom := by
      rw [hQuotient]
    _ = (coarseScalarIso).hom ≫ (isoAt W₁ hW).hom := hScalarW
    _ = ((coarseScalarIso).hom ≫ (isoAt V hV).hom) ≫ (eVW).hom := by
      rw [Category.assoc, hIntegral]
    _ = (restriction).map (quotientIsoAt V hV).hom ≫
        ((scalarAt V hV).hom ≫ (eVW).hom) := by
      rw [← hScalarV, Category.assoc]

/-- The full independent-cover comparison agrees before and after scalar restriction. -/
theorem cmHarrisSuccessiveRefinementScalar_iso :
    (restriction).mapIso (quotientCompareAt V W₁ hV hW) ≪≫ scalarAt W₁ hW =
      scalarAt V hV ≪≫ eVW := by
  apply Iso.ext
  exact cmHarrisSuccessiveRefinementScalar_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V W₁ hV hW

local notation "T" => smallCMCommonLevel D V W₁
local notation "hTV" => smallCMCommonLevel_le_left D V W₁
local notation "hTW" => smallCMCommonLevel_le_right D V W₁
set_option quotPrecheck false in
local notation "hT" => (smallCMCommonLevel_le_left D V W₁).trans hV
local notation "compareAt" => cmHarrisSuccessiveRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "integralSuccessiveCover" => cmHarrisSuccessiveRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "successiveAction" => cmHarrisSuccessiveRefinementIntegralActionIso D U ρ p m hm k
local notation "aVT" => integralSuccessiveCover V T hV hT hTV
local notation "aWT" => integralSuccessiveCover W₁ T hW hT hTW
local notation "φVT" => smallCMResidualQuotientMap D U V T hTV
local notation "φWT" => smallCMResidualQuotientMap D U W₁ T hTW
set_option quotPrecheck false in
local notation "rVT" => etaleCrossCoverMap X φVT aVT (successiveAction V T hV hT hTV).hom
set_option quotPrecheck false in
local notation "rWT" => etaleCrossCoverMap X φWT aWT (successiveAction W₁ T hW hT hTW).hom

/-- Actual restriction from the first cover to the constructed common cover is invertible. -/
theorem cmHarrisCommonRefinementIntegralLeftMap_isIso : IsIso rVT := by
  rw [← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V T hV hT hTV]
  infer_instance

/-- Actual restriction from the second cover to the constructed common cover is invertible. -/
theorem cmHarrisCommonRefinementIntegralRightMap_isIso : IsIso rWT := by
  rw [← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k W₁ T hW hT hTW]
  infer_instance

/-- Compare unrelated normal covers by their actual cross-cover maps to the common intersection. -/
def cmHarrisCommonRefinementIntegralIso : sheafAt V hV ≅ sheafAt W₁ hW := by
  letI : IsIso rVT := cmHarrisCommonRefinementIntegralLeftMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV
  letI : IsIso rWT := cmHarrisCommonRefinementIntegralRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  exact asIso rVT ≪≫ (asIso rWT).symm

local notation "eCommon" => cmHarrisCommonRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW

/-- Restriction to the actual common cover normalizes the common-refinement comparison. -/
@[reassoc] theorem cmHarrisCommonRefinementIntegralIso_hom_comp :
    (eCommon).hom ≫ rWT = rVT := by
  have : IsIso rWT := cmHarrisCommonRefinementIntegralRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  change (rVT ≫ inv rWT) ≫ rWT = rVT
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Comparison via the common cover is the canonical independent-cover comparison. -/
theorem cmHarrisCommonRefinementIntegralIso_eq_successive :
    eCommon = compareAt V W₁ hV hW := by
  have : IsIso rWT := cmHarrisCommonRefinementIntegralRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  apply Iso.ext
  apply (cancel_mono rWT).1
  rw [cmHarrisCommonRefinementIntegralIso_hom_comp]
  rw [← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k W₁ T hW hT hTW,
    ← cmHarrisSuccessiveRefinementIntegralIso_hom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V T hV hT hTV]
  exact (cmHarrisSuccessiveRefinementIntegralIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW T hT).symm

/-- The canonical independent-cover comparison agrees after actual restriction to the common cover. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIntegralIso_common_comp :
    (compareAt V W₁ hV hW).hom ≫ rWT = rVT := by
  rw [← cmHarrisCommonRefinementIntegralIso_eq_successive D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW]
  exact cmHarrisCommonRefinementIntegralIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW

/-- The actual common-cover restriction equation uniquely characterizes the forward comparison. -/
theorem cmHarrisCommonRefinementIntegralIso_hom_unique
    (f : sheafAt V hV ⟶ sheafAt W₁ hW) (hf : f ≫ rWT = rVT) :
    f = (eCommon).hom := by
  have : IsIso rWT := cmHarrisCommonRefinementIntegralRightMap_isIso D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW
  apply (cancel_mono rWT).1
  exact hf.trans (cmHarrisCommonRefinementIntegralIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW).symm

local notation "quotientCommon" => cmHarrisCommonRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW

/-- Actual comparison through the common cover commutes with quotient-ring scalar restriction. -/
@[reassoc] theorem cmHarrisCommonRefinementScalar_square :
    (restriction).map (quotientCommon).hom ≫ (scalarAt W₁ hW).hom =
      (scalarAt V hV).hom ≫ (eCommon).hom := by
  rw [cmHarrisCommonRefinementIso_eq_successive D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V W₁ hV hW,
    cmHarrisCommonRefinementIntegralIso_eq_successive D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V W₁ hV hW]
  exact cmHarrisSuccessiveRefinementScalar_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V W₁ hV hW

/-- The complete common-cover isomorphisms agree before and after scalar restriction. -/
theorem cmHarrisCommonRefinementScalar_iso :
    (restriction).mapIso quotientCommon ≪≫ scalarAt W₁ hW =
      scalarAt V hV ≪≫ eCommon := by
  apply Iso.ext
  exact cmHarrisCommonRefinementScalar_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V W₁ hV hW

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
