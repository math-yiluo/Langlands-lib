import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientRefinementScalars

/-! # Integral evaluation on refined original CM coefficient covers -/

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

local notation "fineIntegralAction" => cmHarrisRefinementIntegralAction D U ρ p m hm k V hV
local notation "fineIntegralSheaf" => cmHarrisRefinementIntegralSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "fineIntegralInclusion" => cmHarrisRefinementIntegralInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "constantIntegral" => (constantSheaf J (ModuleCat.{0} R)).obj (integralAction).V
local notation "constantIntegralAction" =>
  ((constantSheaf J (ModuleCat.{0} R)).mapAction
    (SmallCMResidualGroup D U Vcoeff)).obj integralAction
local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "systemInclusion" => cmHarrisCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid (op k)
local notation "integralIso" => cmHarrisRefinementIntegralIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "localize" => (J).overPullback (ModuleCat.{0} R) (Z).val.V

/-- Canonical invariant evaluation of the independently descended integral fine sheaf. -/
def cmHarrisRefinementIntegralTrivialization :
    (localize).obj fineIntegralSheaf ≅ (localize).obj constantIntegral :=
  (constantAssociatedTrivializationOfSplitting J (Z).val
    (etaleTorsorSectionSplitting X _ (Z).val (Z).property R)).app fineIntegralAction

local notation "fineTrivialization" => cmHarrisRefinementIntegralTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k V hV

/-- The forward map evaluates the actual invariant inclusion on the tautological graph. -/
theorem cmHarrisRefinementIntegralTrivialization_hom :
    (fineTrivialization).hom =
      (localize).map fineIntegralInclusion ≫
        productEvaluation J (Z).val constantIntegral := rfl

/-- Original integral coefficient-cover evaluation along the actual refinement map. -/
def cmHarrisIntegralTrivializationAlongRefinement :
    (localize).obj ((system).obj (op k)) ≅ (localize).obj constantIntegral :=
  (associatedTrivializationAlongOfSplitting J (Y).val (a).hom
    (etaleTorsorSectionSplitting X _ (Y).val (Y).property R)).app constantIntegralAction

local notation "alongTrivialization" => cmHarrisIntegralTrivializationAlongRefinement D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k V hV

/-- This original-cover trivialization is constructed by evaluation along forgetting. -/
theorem cmHarrisIntegralTrivializationAlongRefinement_hom :
    (alongTrivialization).hom =
      associatedEvaluationAlong J (Y).val (a).hom constantIntegralAction := rfl

/-- Integral refinement preserves canonical evaluation along the original forgetting map. -/
@[reassoc] theorem cmHarrisRefinementIntegralIso_evaluation :
    (localize).map (integralIso).hom ≫ (fineTrivialization).hom =
      (alongTrivialization).hom := by
  change (localize).map (integralIso).hom ≫
      ((localize).map fineIntegralInclusion ≫
        productEvaluation J (Z).val constantIntegral) =
    (localize).map systemInclusion ≫
      productEvaluationAlong J (a).hom constantIntegral
  rw [← Category.assoc, ← Functor.map_comp,
    cmHarrisRefinementIntegralIso_hom_inclusion, Functor.map_comp,
    Category.assoc, coverPullback_productEvaluation]

/-- Both complete local isomorphisms, including the inverse maps, coincide. -/
theorem cmHarrisRefinementIntegralIso_trivialization :
    (localize).mapIso integralIso ≪≫ fineTrivialization = alongTrivialization := by
  apply Iso.ext
  exact cmHarrisRefinementIntegralIso_evaluation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV

local notation "fineQuotientSheaf" => cmHarrisRefinementCoefficientSheaf D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "fineQuotientInclusion" => cmHarrisRefinementCoefficientInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "fineScalarIso" => cmHarrisRefinementSheafRestrictIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV
local notation "constantComparison" => (constantRestrictScalarsIso J quotientMap).app (Mcoeff).V
local notation "fineQuotientTrivialization" => cmHarrisRefinementCoefficientTrivialization
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k V hV
local notation "localRestrict" => sheafCompose ((J).over (Z).val.V)
  (ModuleCat.restrictScalars.{0} quotientMap)

/-- Restrict the independently constructed quotient-ring evaluation to integral scalars. -/
def cmHarrisRefinementRestrictedTrivialization :
    (localize).obj ((restriction).obj fineQuotientSheaf) ≅
      (localize).obj constantIntegral :=
  (localRestrict).mapIso fineQuotientTrivialization ≪≫
    (localize).mapIso constantComparison

local notation "restrictedTrivialization" => cmHarrisRefinementRestrictedTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  existence geometry hRigid ρ p m hm k V hV

/-- The fine scalar comparison preserves actual local evaluation. -/
@[reassoc] theorem cmHarrisRefinementSheafRestrictIso_evaluation :
    (localize).map (fineScalarIso).hom ≫ (fineTrivialization).hom =
      (restrictedTrivialization).hom := by
  let loc := localize
  let c := (constantComparison).hom
  let F := (restriction).obj
    ((constantSheaf J (ModuleCat.{0} Rcoeff)).obj (Mcoeff).V)
  let F' := constantIntegral
  let b := (restriction).map fineQuotientInclusion
  have hi := cmHarrisRefinementSheafRestrictIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hi' := congrArg (fun f => loc.map f) hi
  have hi'' := ((loc.map_comp _ _).symm.trans hi').trans (loc.map_comp _ _)
  have hn := productEvaluation_natural J (Z).val c
  change loc.map (fineScalarIso).hom ≫
      (loc.map fineIntegralInclusion ≫ productEvaluation J (Z).val F') = _
  calc
    _ = (loc.map (fineScalarIso).hom ≫ loc.map fineIntegralInclusion) ≫
        productEvaluation J (Z).val F' := (Category.assoc _ _ _).symm
    _ = (loc.map b ≫ loc.map ((productSheaf J (Z).val.V).map c)) ≫
        productEvaluation J (Z).val F' :=
      congrArg (fun f => f ≫ productEvaluation J (Z).val F') hi''
    _ = loc.map b ≫ (loc.map ((productSheaf J (Z).val.V).map c) ≫
        productEvaluation J (Z).val F') := Category.assoc _ _ _
    _ = loc.map b ≫ (productEvaluation J (Z).val F ≫ loc.map c) :=
      congrArg (fun f => loc.map b ≫ f) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- Equality of the complete fine scalar-compatible evaluation isomorphisms. -/
theorem cmHarrisRefinementSheafRestrictIso_trivialization :
    (localize).mapIso fineScalarIso ≪≫ fineTrivialization = restrictedTrivialization := by
  apply Iso.ext
  exact cmHarrisRefinementSheafRestrictIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV

/-- The inverse fine scalar comparison also preserves canonical evaluation. -/
@[reassoc] theorem cmHarrisRefinementSheafRestrictIso_inv_evaluation :
    (localize).map (fineScalarIso).inv ≫ (restrictedTrivialization).hom =
      (fineTrivialization).hom := by
  rw [← cmHarrisRefinementSheafRestrictIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, (localize).map_id, Category.id_comp]

local notation "coarseScalarIso" => cmHarrisCoefficientSheafRestrictIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k
local notation "quotientIso" => cmHarrisCoefficientRefinementIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k V hV

/-- Scalar restriction and cover refinement agree after original local evaluation. -/
@[reassoc] theorem cmHarrisRefinementScalar_evaluation :
    (localize).map ((restriction).map (quotientIso).hom) ≫
        (restrictedTrivialization).hom =
      (localize).map (coarseScalarIso).hom ≫ (alongTrivialization).hom := by
  have hFine := cmHarrisRefinementSheafRestrictIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hSquare := cmHarrisRefinementScalar_square D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hIntegral := cmHarrisRefinementIntegralIso_evaluation D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV
  have hMapped :
      (localize).map ((restriction).map (quotientIso).hom) ≫
          (localize).map (fineScalarIso).hom =
        (localize).map (coarseScalarIso).hom ≫ (localize).map (integralIso).hom :=
    ((localize).map_comp _ _).symm.trans
      ((congrArg (fun f => (localize).map f) hSquare).trans
        ((localize).map_comp _ _))
  calc
    _ = (localize).map ((restriction).map (quotientIso).hom) ≫
        ((localize).map (fineScalarIso).hom ≫ (fineTrivialization).hom) :=
      congrArg (fun f => (localize).map ((restriction).map (quotientIso).hom) ≫ f)
        hFine.symm
    _ = ((localize).map ((restriction).map (quotientIso).hom) ≫
        (localize).map (fineScalarIso).hom) ≫ (fineTrivialization).hom :=
      (Category.assoc _ _ _).symm
    _ = ((localize).map (coarseScalarIso).hom ≫
        (localize).map (integralIso).hom) ≫ (fineTrivialization).hom :=
      congrArg (fun f => f ≫ (fineTrivialization).hom) hMapped
    _ = (localize).map (coarseScalarIso).hom ≫
        ((localize).map (integralIso).hom ≫ (fineTrivialization).hom) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun f => (localize).map (coarseScalarIso).hom ≫ f) hIntegral

/-- The two scalar/refinement evaluation paths give the same complete isomorphism. -/
theorem cmHarrisRefinementScalar_trivialization :
    (localize).mapIso ((restriction).mapIso quotientIso) ≪≫ restrictedTrivialization =
      (localize).mapIso coarseScalarIso ≪≫ alongTrivialization := by
  apply Iso.ext
  exact cmHarrisRefinementScalar_evaluation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid
    ρ p m hm k V hV

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
