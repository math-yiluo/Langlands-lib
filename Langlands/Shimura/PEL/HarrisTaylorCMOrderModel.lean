import Langlands.Shimura.PEL.PolarizedWeilOrderModel
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationFibreAffine
import Langlands.Shimura.PEL.HarrisIntegralOrderModel
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClassImage
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf

/-! # Actual polarized integral models of normalized Harris CM representatives -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

/-- The two actual etale maps in an integral model retain every specified relative
dimension over a characteristic-zero field scheme. -/
theorem IntegralOrderModel.relativeDimension_iff_overField
    {S : Scheme.{u}} {A : AbelianScheme S} {O : Type v} [Ring O]
    {α : O →+* Rationalization.End A} (M : IntegralOrderModel α)
    {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) (g : ℕ) :
    A.HasRelativeDimension g ↔ M.B.HasRelativeDimension g := by
  have hnK : IsUnit (M.inverseData.multiple : K) :=
    isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr M.inverseData.multiple_ne_zero)
  have hnS : IsUnit (M.inverseData.multiple : Γ(S, ⊤)) := by
    simpa only [map_intCast] using hnK.map ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom
  have hmaps := integralInverseData_finiteEtaleIsogenies M.inverseData M.multiple_pos hnS
  have : Etale (hom M.inverseData.hom) := hmaps.2.1
  have : Etale (hom M.inverseData.inv) := hmaps.2.2.2
  constructor
  · intro hA
    let : SmoothOfRelativeDimension g A.X.hom := hA
    have h : SmoothOfRelativeDimension (0 + g) (hom M.inverseData.inv ≫ A.X.hom) :=
      inferInstance
    simpa only [zero_add, Over.w] using h
  · intro hB
    let : SmoothOfRelativeDimension g M.B.X.hom := hB
    have h : SmoothOfRelativeDimension (0 + g) (hom M.inverseData.hom ≫ M.B.X.hom) :=
      inferInstance
    simpa only [zero_add, Over.w] using h

end Langlands.AbelianScheme

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

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
  (P : Prerequisites.{0})
  (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (htor : TorsionFiniteEtaleStatement.{0})
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (X : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    (S := Z.obj.left))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "reflex" => D.harrisTaylorReflexStructure C Z.obj.hom
local notation "hfib" => DualWitness.forall_finset_fibre_affine P fibreAmple
  (PolarizedWeilLevel.PolarizedAction.dualWitness P X) X.polarization X.isPolarization

/-- Construct the actual Harris order model using the fixed polarization bundle;
the generic proper-family fibre-ampleness theorem remains explicit. -/
def cmIntegralOrderModel :
    letI := auxiliaryStarRing D C
    IntegralOrderModel (D.harrisRationalOrderAction C X.actionObj.abelianScheme
      X.actionObj.action) := by
  letI := auxiliaryStarRing D C
  exact D.harrisIntegralOrderModel C htor reflex
    X.actionObj.abelianScheme X.actionObj.action hfib

local notation "M" => cmIntegralOrderModel D C P fibreAmple htor Z X

/-- Select the model's actual dual data from the existing admissible test base. -/
def cmIntegralOrderModelDualWitness : DualWitness (M).B := by
  let W := Classical.choice (Z.property.dualExists (M).B)
  exact ⟨W.hasDual, W.geometry, W.inversePoincare, W.evaluation⟩

local notation "W" => cmIntegralOrderModelDualWitness D C P fibreAmple htor Z X

/-- The constructed model is an actual faithful polarized action with the original
positive auxiliary involution. -/
def cmPolarizedOrderModel :
    PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := Z.obj.left) := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.orderModel P basisO X M W Z.obj.hom

local notation "Y" => cmPolarizedOrderModel D C P fibreAmple htor Z X

/-- The comparison uses the actual model isogeny and its exact rational inverse. -/
def cmPolarizedOrderModelIso :
    letI := auxiliaryStarRing D C
    X.actionObj ≅ (Y).actionObj := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.orderModelIso P basisO X M W Z.obj.hom

/-- The integral action lives on this very polarized representative. -/
def cmPolarizedOrderModelRestriction :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (D.harrisHodgePELIntegralOrder C) Y := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.orderModelRestriction P basisO X M W Z.obj.hom

omit [IsCMField F] in
/-- The unchanged normalized CM determinant and actual dimension hold on the model
if and only if they hold on the original representative. -/
theorem cmPolarizedOrderModel_condition_iff :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
        X.actionObj.abelianScheme X.actionObj.action ↔
      D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
        (Y).actionObj.abelianScheme (Y).actionObj.action := by
  let := auxiliaryStarRing D C
  apply and_congr
  · exact D.harrisTaylorCMRationalLieDeterminantCondition_iso C Z.obj.hom
      X.actionObj.action (Y).actionObj.action
      (RationalAlgebraAction.underlyingIso
        (cmPolarizedOrderModelIso D C P fibreAmple htor Z X))
      (RationalAlgebraAction.intertwines
        (cmPolarizedOrderModelIso D C P fibreAmple htor Z X).hom)
  · exact IntegralOrderModel.relativeDimension_iff_overField M Z.obj.hom _

/-- The actual comparison carries the positive square of the same integral inverse
multiple as its exact polarization multiplier. -/
def cmPolarizedOrderModelMultiplier : ℚˣ :=
  Units.mk0 (((M).inverseData.multiple : ℚ) ^ 2)
    (pow_ne_zero _ (Int.cast_ne_zero.mpr (M).inverseData.multiple_ne_zero))

local notation "q" => cmPolarizedOrderModelMultiplier D C P fibreAmple htor Z X

omit [IsCMField F] in
/-- Positivity retains the original ordering on rational multipliers. -/
theorem cmPolarizedOrderModelMultiplier_pos : 0 < (q : ℚ) := by
  let := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.orderModelMultiple_pos P X M

omit [IsCMField F] in
/-- The isomorphism is compatible with the actual polarizations and the exact
selected rational multiplier. -/
theorem cmPolarizedOrderModel_multiple :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.Multiple P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability P.square P.universality Z.property.pairAdditivity
      X Y q (cmPolarizedOrderModelIso D C P fibreAmple htor Z X) := by
  let := auxiliaryStarRing D C
  exact PolarizedWeilLevel.PolarizedAction.orderModelMultiple P basisO X M W Z.obj.hom
    Z.property.pairAdditivity

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
