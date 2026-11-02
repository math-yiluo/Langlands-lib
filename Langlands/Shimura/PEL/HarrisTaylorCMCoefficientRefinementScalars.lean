import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientRefinement
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientScalars
import Langlands.Shimura.Coefficients.VaryingSystemCoverChange

/-! # Integral scalars and original CM normal coefficient refinements -/

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

variable (V : SmallCMLevel D)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
  (hV : V.obj.subgroup ≤ (cmHarrisCoefficientLevel D ρ p U m hm k).obj.subgroup)

local notation "hVU" => hV.trans (cmHarrisCoefficientLevel_le D ρ p U m hm k)
local notation "φ" => smallCMResidualQuotientMap D U Vcoeff V hV
local notation "fineAction" => cmHarrisResidualCoefficientAction D ρ p U V m k
  (cmHarrisRefinement_kernel_le D U ρ p m hm k V hV)


local notation "R" => HarrisCoefficientIntegers K p
local notation "quotientMap" => Ideal.Quotient.mk (harrisCoefficientScalarIdeal K p m ^ k)
local notation "restriction" => sheafCompose J (ModuleCat.restrictScalars.{0} quotientMap)
local notation "integralAction" => (cmHarrisCoefficientDiagram D ρ p U m hm).action (Opposite.op k)
local notation "Q" => SmallCMResidualGroup D U V
local notation "Y" => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "Z" => cmHarrisRefinementTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "a" => cmHarrisCoefficientRefinementCover D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

/-- The independently factored fine action with scalars in the fixed integral ring. -/
def cmHarrisRefinementIntegralAction : Action (ModuleCat.{0} R) Q :=
  ((ModuleCat.restrictScalars.{0} quotientMap).mapAction Q).obj fineAction

local notation "fineIntegralAction" => cmHarrisRefinementIntegralAction D U ρ p m hm k V hV

/-- Restricting the original coefficient-diagram action gives the integral fine action. -/
def cmHarrisRefinementIntegralActionIso :
    (Action.res (ModuleCat.{0} R) φ).obj integralAction ≅ fineIntegralAction :=
  Action.mkIso (Iso.refl _) (by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      change (cmHarrisTorsionSystem D ρ p U m |>.obj (Opposite.op k)).ρ g ≫ 𝟙 _ =
        𝟙 _ ≫ (cmHarrisTorsionSystem D ρ p U m |>.obj (Opposite.op k)).ρ g
      simp only [Category.comp_id, Category.id_comp])

@[simp] theorem cmHarrisRefinementIntegralActionIso_hom_hom :
    (cmHarrisRefinementIntegralActionIso D U ρ p m hm k V hV).hom.hom = 𝟙 _ := rfl

/-- Independent invariant descent of the integral coefficient action on the fine cover. -/
def cmHarrisRefinementIntegralSheaf : Sheaf J (ModuleCat.{0} R) :=
  (etaleAssociatedFunctor X (Z).val).obj fineIntegralAction

local notation "fineIntegralSheaf" => cmHarrisRefinementIntegralSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "constantIntegral" => (constantSheaf J (ModuleCat.{0} R)).obj (integralAction).V

/-- The actual invariant-section inclusion for the integral fine-cover construction. -/
def cmHarrisRefinementIntegralInclusion :
    fineIntegralSheaf ⟶ (productSheaf J (Z).val.V).obj constantIntegral :=
  etaleAssociatedInclusion X (Z).val fineIntegralAction

instance cmHarrisRefinementIntegralInclusion_mono :
    Mono (cmHarrisRefinementIntegralInclusion D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U existence geometry hRigid
      ρ p m hm k V hV) := by
  change Mono (etaleAssociatedInclusion X (Z).val fineIntegralAction)
  infer_instance

local notation "fineIntegralInclusion" => cmHarrisRefinementIntegralInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "systemInclusion" => cmHarrisCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid (Opposite.op k)
local notation "actionIso" => cmHarrisRefinementIntegralActionIso D U ρ p m hm k V hV

/-- The actual integral cross-cover comparison, with invertibility proved from the torsors. -/
def cmHarrisRefinementIntegralIso : (system).obj (Opposite.op k) ≅ fineIntegralSheaf := by
  let e := etaleCrossCoverMap X φ a
    (𝟙 ((Action.res (ModuleCat.{0} R) φ).obj integralAction))
  haveI : IsIso e := etaleAssociatedCoverComparison X _ _ (Y).val (Z).val
    (Y).property (Z).property φ a R integralAction
  exact asIso e ≪≫ (etaleAssociatedFunctor X (Z).val).mapIso actionIso

local notation "integralIso" => cmHarrisRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

/-- Integral refinement restricts actual sections along the original scheme-forgetting map. -/
@[reassoc] theorem cmHarrisRefinementIntegralIso_hom_inclusion :
    (integralIso).hom ≫ fineIntegralInclusion =
      systemInclusion ≫ coverPullback J (a).hom constantIntegral := by
  have hn := etaleAssociatedInclusion_natural X (Z).val (actionIso).hom
  have hn' : (etaleAssociatedFunctor X (Z).val).map (actionIso).hom ≫
      fineIntegralInclusion = etaleAssociatedInclusion X (Z).val
        ((Action.res (ModuleCat.{0} R) φ).obj integralAction) := by
    change (etaleAssociatedFunctor X (Z).val).map (actionIso).hom ≫
        etaleAssociatedInclusion X (Z).val fineIntegralAction =
      etaleAssociatedInclusion X (Z).val
        ((Action.res (ModuleCat.{0} R) φ).obj integralAction)
    change (etaleAssociatedFunctor X (Z).val).map (actionIso).hom ≫
        etaleAssociatedInclusion X (Z).val fineIntegralAction =
      etaleAssociatedInclusion X (Z).val
        ((Action.res (ModuleCat.{0} R) φ).obj integralAction) ≫
        (productSheaf J (Z).val.V).map
          ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hn
    have hp := congrArg (fun b => (productSheaf J (Z).val.V).map b)
      ((constantSheaf J (ModuleCat.{0} R)).map_id (integralAction).V)
    have hp' := hp.trans ((productSheaf J (Z).val.V).map_id _)
    exact hn.trans ((congrArg (fun b => etaleAssociatedInclusion X (Z).val
      ((Action.res (ModuleCat.{0} R) φ).obj integralAction) ≫ b)
      hp').trans (Category.comp_id _))
  change (etaleCrossCoverMap X φ a
    (𝟙 ((Action.res (ModuleCat.{0} R) φ).obj integralAction)) ≫
      (etaleAssociatedFunctor X (Z).val).map (actionIso).hom) ≫ fineIntegralInclusion = _
  rw [Category.assoc, hn']
  exact etaleCrossCoverMap_identity_inclusion X R φ a integralAction

local notation "fineQuotientSheaf" => cmHarrisRefinementCoefficientSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "fineQuotientInclusion" => cmHarrisRefinementCoefficientInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

/-- Fine-cover invariant descent commutes with the actual quotient-ring scalar restriction. -/
def cmHarrisRefinementSheafRestrictIso :
    (restriction).obj fineQuotientSheaf ≅ fineIntegralSheaf :=
  (constantAssociatedRestrictScalarsIso J quotientMap (Z).val).app fineAction

local notation "fineScalarIso" => cmHarrisRefinementSheafRestrictIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "constantComparison" => (constantRestrictScalarsIso J quotientMap).app (Mcoeff).V

/-- The fine scalar comparison carries the original invariant inclusion. -/
@[reassoc] theorem cmHarrisRefinementSheafRestrictIso_hom_inclusion :
    (fineScalarIso).hom ≫ fineIntegralInclusion =
      (restriction).map fineQuotientInclusion ≫
        (productSheaf J (Z).val.V).map (constantComparison).hom :=
  constantAssociatedRestrictScalarsIso_hom_inclusion J quotientMap (Z).val fineAction

local notation "coarseScalarIso" => cmHarrisCoefficientSheafRestrictIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k
local notation "quotientIso" => cmHarrisCoefficientRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "coarseQuotientInclusion" => cmHarrisCoefficientInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "constantQuotient" => (constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V

/-- Original cover refinement and quotient-ring scalar restriction commute as sheaf maps. -/
@[reassoc] theorem cmHarrisRefinementScalar_square :
    (restriction).map (quotientIso).hom ≫ (fineScalarIso).hom =
      (coarseScalarIso).hom ≫ (integralIso).hom := by
  apply (cancel_mono fineIntegralInclusion).1
  have hFine := cmHarrisRefinementSheafRestrictIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hIntegral := cmHarrisRefinementIntegralIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hCoarse := cmHarrisCoefficientSheafRestrictIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k
  have hQuotient := cmHarrisCoefficientRefinementIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hMapped :
      (restriction).map (quotientIso).hom ≫ (restriction).map fineQuotientInclusion =
        (restriction).map coarseQuotientInclusion ≫
          (restriction).map (coverPullback J (a).hom constantQuotient) :=
    ((restriction).map_comp _ _).symm.trans
      ((congrArg (fun b => (restriction).map b) hQuotient).trans
        ((restriction).map_comp _ _))
  have hPullback :
      (restriction).map (coverPullback J (a).hom constantQuotient) ≫
          (productSheaf J (Z).val.V).map (constantComparison).hom =
        (productSheaf J (Y).val.V).map (constantComparison).hom ≫
          coverPullback J (a).hom constantIntegral := by
    change coverPullback J (a).hom ((restriction).obj constantQuotient) ≫
        (productSheaf J (Z).val.V).map (constantComparison).hom = _
    exact coverPullback_natural J (a).hom (constantComparison).hom
  calc
    ((restriction).map (quotientIso).hom ≫ (fineScalarIso).hom) ≫ fineIntegralInclusion =
        (restriction).map (quotientIso).hom ≫
          ((restriction).map fineQuotientInclusion ≫
            (productSheaf J (Z).val.V).map (constantComparison).hom) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun b => (restriction).map (quotientIso).hom ≫ b) hFine)
    _ = ((restriction).map coarseQuotientInclusion ≫
          (restriction).map (coverPullback J (a).hom constantQuotient)) ≫
            (productSheaf J (Z).val.V).map (constantComparison).hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun b => b ≫ (productSheaf J (Z).val.V).map (constantComparison).hom)
          hMapped)
    _ = (restriction).map coarseQuotientInclusion ≫
        ((productSheaf J (Y).val.V).map (constantComparison).hom ≫
          coverPullback J (a).hom constantIntegral) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun b => (restriction).map coarseQuotientInclusion ≫ b) hPullback)
    _ = ((coarseScalarIso).hom ≫ systemInclusion) ≫
          coverPullback J (a).hom constantIntegral :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun b => b ≫ coverPullback J (a).hom constantIntegral) hCoarse.symm)
    _ = ((coarseScalarIso).hom ≫ (integralIso).hom) ≫ fineIntegralInclusion :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun b => (coarseScalarIso).hom ≫ b) hIntegral.symm).trans
          (Category.assoc _ _ _).symm)

/-- The complete refinement and scalar comparisons give the same isomorphism. -/
theorem cmHarrisRefinementScalar_iso :
    (restriction).mapIso quotientIso ≪≫ fineScalarIso =
      coarseScalarIso ≪≫ integralIso := by
  apply Iso.ext
  exact cmHarrisRefinementScalar_square D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
