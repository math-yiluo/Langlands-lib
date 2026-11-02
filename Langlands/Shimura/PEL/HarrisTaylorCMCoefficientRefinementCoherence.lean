import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientRefinement

/-! # Coherence of original CM coefficient normal refinements -/

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

variable (V W₁ : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  [(W₁.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (hV : V.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)
  (hW : W₁.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)
  (hWV : W₁.obj.subgroup ≤ V.obj.subgroup)

local notation "φVW" => smallCMResidualQuotientMap D U V W₁ hWV
local notation "actionV" => cmHarrisResidualCoefficientAction D ρ p U V m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k V hV)
local notation "actionW" => cmHarrisResidualCoefficientAction D ρ p U W₁ m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k W₁ hW)

/-- Successive normal refinements retain the independently factored coefficient action. -/
def cmHarrisSuccessiveRefinementActionIso :
    (Action.res (ModuleCat.{0} Rcoeff) φVW).obj actionV ≅ actionW :=
  Action.mkIso (Iso.refl _) (by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (cmHarrisFiniteTorsionAction D ρ p U m k).ρ g ≫ 𝟙 _ =
        𝟙 _ ≫ (cmHarrisFiniteTorsionAction D ρ p U m k).ρ g
      simp only [Category.comp_id, Category.id_comp])

@[simp] theorem cmHarrisSuccessiveRefinementActionIso_hom_hom :
    (cmHarrisSuccessiveRefinementActionIso D U ρ p m hm k V W₁ hV hW hWV).hom.hom =
      𝟙 _ := rfl

@[simp] theorem cmHarrisSuccessiveRefinementActionIso_inv_hom :
    (cmHarrisSuccessiveRefinementActionIso D U ρ p m hm k V W₁ hV hW hWV).inv.hom =
      𝟙 _ := rfl

/-- Actual scheme forgetting between arbitrary normal covers below the coefficient kernel. -/
def cmHarrisSuccessiveRefinementCover :
    (torsorAt W₁ hW).val ⟶
      (Action.res (X).Etale φVW).obj (torsorAt V hV).val where
  hom := MorphismProperty.Over.homMk ((schemes q).map (smallCMInclusion D hWV)) (by
    change (schemes q).map (smallCMInclusion D hWV) ≫
        (schemes q).map (smallCMInclusion D
          (hV.trans (cmHarrisCoefficientLevel_le D ρ p U m hm k))) =
      (schemes q).map (smallCMInclusion D
        (hW.trans (cmHarrisCoefficientLevel_le D ρ p U m hm k)))
    rw [← (schemes q).map_comp, smallCMInclusion_trans])
  comm g := by
    apply MorphismProperty.Over.Hom.ext
    exact (cmNormalRefinement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U V W₁
      (hV.trans (cmHarrisCoefficientLevel_le D ρ p U m hm k)) hWV q).comm g

local notation "aVW" => cmHarrisSuccessiveRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW hWV
local notation "cVW" => cmHarrisSuccessiveRefinementActionIso D U ρ p m hm k
  V W₁ hV hW hWV

@[simp] theorem cmHarrisSuccessiveRefinementCover_left :
    (aVW).hom.left = (schemes q).map (smallCMInclusion D hWV) := rfl

/-- Both routes from the finer cover to the original coefficient-kernel cover coincide. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementCover_triangle :
    (aVW).hom ≫ (coverAt V hV).hom = (coverAt W₁ hW).hom := by
  apply MorphismProperty.Over.Hom.ext
  change (schemes q).map (smallCMInclusion D hWV) ≫
    (schemes q).map (smallCMInclusion D hV) =
    (schemes q).map (smallCMInclusion D hW)
  rw [← (schemes q).map_comp, smallCMInclusion_trans]

local notation "reps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- Successive cover forgetting remains over the original CM field. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementCover_over :
    (aVW).hom.left ≫ ((reps) V).base.obj.hom = ((reps) W₁).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor reps (smallCMInclusion D hWV)

/-- Compare two independently constructed fine-cover sheaves through their canonical comparisons. -/
def cmHarrisSuccessiveRefinementIso : sheafAt V hV ≅ sheafAt W₁ hW :=
  (isoAt V hV).symm ≪≫ isoAt W₁ hW

local notation "eVW" => cmHarrisSuccessiveRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V W₁ hV hW

/-- The comparison restricts cover sections along the original intermediate forgetting map. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_hom_inclusion :
    (eVW).hom ≫ inclusionAt W₁ hW =
      inclusionAt V hV ≫ coverPullback J (aVW).hom constantModule := by
  change ((isoAt V hV).inv ≫ (isoAt W₁ hW).hom) ≫ inclusionAt W₁ hW = _
  rw [Category.assoc, cmHarrisCoefficientRefinementIso_hom_inclusion,
    ← cmHarrisSuccessiveRefinementCover_triangle D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V W₁ hV hW hWV,
    coverPullback_comp]
  simpa only [Category.assoc] using
    cmHarrisCoefficientRefinementIso_inv_inclusion_assoc D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U existence geometry
      hRigid ρ p m hm k V hV (coverPullback J (aVW).hom constantModule)

/-- The forward comparison is exactly the cross-cover map for actual forgetting and identity coefficients. -/
theorem cmHarrisSuccessiveRefinementIso_hom :
    (eVW).hom = etaleCrossCoverMap X φVW aVW (cVW).hom := by
  let c := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U W₁)).map (cVW).hom
  have hc : c.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} Rcoeff)).map (𝟙 (Mcoeff).V) = _
    exact (constantSheaf J (ModuleCat.{0} Rcoeff)).map_id _
  have he := crossCoverMap_inclusion (R := Rcoeff) J φVW aVW
    (F := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
      (SmallCMResidualGroup D U V)).obj actionV)
    (E := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
      (SmallCMResidualGroup D U W₁)).obj actionW) c
  have hid : (productSheaf J (torsorAt W₁ hW).val.V).map (𝟙 constantModule) = 𝟙 _ :=
    (productSheaf J (torsorAt W₁ hW).val.V).map_id constantModule
  erw [hc, hid] at he
  have he' := he.trans (congrArg (fun b =>
    inclusionAt V hV ≫ b) (Category.comp_id
      (coverPullback J (aVW).hom constantModule)))
  apply Langlands.Shimura.Coefficients.hom_ext J (torsorAt W₁ hW).val
  exact (cmHarrisSuccessiveRefinementIso_hom_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV).trans he'.symm

/-- The inverse is normalized by restriction along the same intermediate forgetting map. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_inv_inclusion :
    (eVW).inv ≫ inclusionAt V hV ≫ coverPullback J (aVW).hom constantModule =
      inclusionAt W₁ hW := by
  rw [← cmHarrisSuccessiveRefinementIso_hom_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW hWV]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Comparing through any intermediate normal cover gives the original comparison. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_triangle :
    (isoAt V hV).hom ≫ (eVW).hom = (isoAt W₁ hW).hom := by
  change (isoAt V hV).hom ≫ ((isoAt V hV).inv ≫ (isoAt W₁ hW).hom) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Identity forgetting at a normal coefficient level is the identity site morphism. -/
@[simp] theorem cmHarrisSuccessiveRefinementCover_refl :
    (cmHarrisSuccessiveRefinementCover D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V V hV hV (le_refl _)).hom = 𝟙 (torsorAt V hV).val.V := by
  apply MorphismProperty.Over.Hom.ext
  change (schemes q).map (smallCMInclusion D (le_refl _)) = 𝟙 _
  rw [smallCMInclusion_refl, (schemes q).map_id]

/-- A level compared with itself has the identity coefficient comparison. -/
@[simp] theorem cmHarrisSuccessiveRefinementIso_refl :
    cmHarrisSuccessiveRefinementIso D C preservation composition unitCoherence
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
local notation "eW₂" => cmHarrisSuccessiveRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k W₁ V₂ hW h₂
local notation "eV₂" => cmHarrisSuccessiveRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V V₂ hV h₂

/-- Successive original forgetting maps equal direct forgetting on the actual site objects. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementCover_comp :
    (aW₂).hom ≫ (aVW).hom = (aV₂).hom := by
  apply MorphismProperty.Over.Hom.ext
  change (schemes q).map (smallCMInclusion D h₂W) ≫
    (schemes q).map (smallCMInclusion D hWV) =
    (schemes q).map (smallCMInclusion D (h₂W.trans hWV))
  rw [← (schemes q).map_comp, smallCMInclusion_trans]

/-- Successive comparisons of independent normal-cover sheaves agree with direct comparison. -/
theorem cmHarrisSuccessiveRefinementIso_comp :
    eVW ≪≫ eW₂ = eV₂ := by
  apply Iso.ext
  change ((isoAt V hV).inv ≫ (isoAt W₁ hW).hom) ≫
    ((isoAt W₁ hW).inv ≫ (isoAt V₂ h₂).hom) =
    (isoAt V hV).inv ≫ (isoAt V₂ h₂).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The forward module-sheaf maps satisfy the same strict composition equation. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_hom_comp :
    (eVW).hom ≫ (eW₂).hom = (eV₂).hom :=
  congrArg Iso.hom (cmHarrisSuccessiveRefinementIso_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW V₂ h₂)

local notation "cW₂" => cmHarrisSuccessiveRefinementActionIso D U ρ p m hm k
  W₁ V₂ hW h₂ h₂W
local notation "cV₂" => cmHarrisSuccessiveRefinementActionIso D U ρ p m hm k
  V V₂ hV h₂ (h₂W.trans hWV)

/-- The actual cross-cover maps for successive original refinements compose to direct forgetting. -/
@[reassoc] theorem cmHarrisSuccessiveCrossCoverMap_comp :
    etaleCrossCoverMap X φVW aVW (cVW).hom ≫
      etaleCrossCoverMap X (smallCMResidualQuotientMap D U W₁ V₂ h₂W) aW₂ (cW₂).hom =
    etaleCrossCoverMap X (smallCMResidualQuotientMap D U V V₂ (h₂W.trans hWV))
      aV₂ (cV₂).hom := by
  rw [← cmHarrisSuccessiveRefinementIso_hom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V W₁ hV hW hWV,
    ← cmHarrisSuccessiveRefinementIso_hom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k W₁ V₂ hW h₂ h₂W,
    ← cmHarrisSuccessiveRefinementIso_hom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V V₂ hV h₂ (h₂W.trans hWV)]
  exact cmHarrisSuccessiveRefinementIso_hom_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry
    hRigid ρ p m hm k V W₁ hV hW V₂ h₂

/-- Successive comparison intertwines fine evaluation with evaluation along original forgetting. -/
@[reassoc] theorem cmHarrisSuccessiveRefinementIso_evaluation :
    ((J).overPullback (ModuleCat.{0} Rcoeff) (torsorAt W₁ hW).val.V).map (eVW).hom ≫
        (trivializationAt W₁ hW).hom =
      associatedEvaluationAlong J (torsorAt V hV).val (aVW).hom
        (((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
          (SmallCMResidualGroup D U V)).obj actionV) := by
  let c := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    (SmallCMResidualGroup D U W₁)).map (cVW).hom
  have hc : c.hom = 𝟙 constantModule := by
    change (constantSheaf J (ModuleCat.{0} Rcoeff)).map (𝟙 (Mcoeff).V) = _
    exact (constantSheaf J (ModuleCat.{0} Rcoeff)).map_id _
  have he := crossCoverMap_evaluation (R := Rcoeff) J φVW aVW
    (F := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
      (SmallCMResidualGroup D U V)).obj actionV)
    (E := ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
      (SmallCMResidualGroup D U W₁)).obj actionW) c
  have hid : ((J).overPullback (ModuleCat.{0} Rcoeff) (torsorAt W₁ hW).val.V).map
      (𝟙 constantModule) = 𝟙 _ :=
    ((J).overPullback (ModuleCat.{0} Rcoeff) (torsorAt W₁ hW).val.V).map_id constantModule
  erw [hc, hid] at he
  have he' := he.trans (Category.comp_id _)
  rw [cmHarrisSuccessiveRefinementIso_hom D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V W₁ hV hW hWV]
  exact he'

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
