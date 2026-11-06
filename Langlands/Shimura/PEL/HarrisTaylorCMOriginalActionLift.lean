import Langlands.Shimura.PEL.HarrisIntegralCMRosatiReflection
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClassImage
import Langlands.Shimura.PEL.PolarizedWeilOrderModel
import Langlands.GroupScheme.Cartier.RelativeHomFunctoriality

/-! # Original integral CM representatives in the actual closed action locus -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

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
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ Z.obj.left)
  (hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "Rep" => IntegralCMRepresentative D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits
local notation "O" => D.harrisHodgePELIntegralOrder C

variable {U : HarrisLevel D}
  (x : IntegralCMRepresentative D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
    Z.obj.hom compatibility h s hs htor Z.property.torsionUnits U)

local notation "B" => x.data.1.actionObj.abelianScheme
local notation "W" => PolarizedWeilLevel.PolarizedAction.dualWitness P x.data.1
local notation "lam" => x.data.1.polarization

omit [IsCMField F] in
/-- The integral restriction extends to the original rational action on this very
representative; no replacement action or isogeny is chosen. -/
theorem integralCMRepresentative_rationalAction :
    letI := auxiliaryStarRing D C
    D.harrisHodgePELRationalAction C B x.restriction.action = x.data.1.actionObj.action := by
  let _ := auxiliaryStarRing D C
  exact D.harrisHodgePELRationalAction_unique C B x.restriction.action
    x.data.1.actionObj.action (fun a => (x.restriction.agrees a).symm)

local notation "extension_eq" => integralCMRepresentative_rationalAction D C P Z
  compatibility h s hs htor x

omit [IsCMField F] in
/-- The original geometric polarization satisfies every actual order Rosati
identity on the same scheme and with the original chosen dual data. -/
theorem integralCMRepresentative_integralRosati :
    letI := auxiliaryStarRing D C
    IntegralRosatiEquations D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability B x.data.1.hasDual
      x.data.1.inversePoincare x.data.1.evaluation x.data.1.geometry
      x.restriction.action lam := by
  let _ := auxiliaryStarRing D C
  apply (rationalAction_involutionCompatible_iff_integral D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    B x.data.1.hasDual x.data.1.dualEndAdditivity x.data.1.inversePoincare
    x.data.1.evaluation x.data.1.geometry Z.property.torsionUnits x.restriction.action lam).mp
  rw [extension_eq]
  exact x.data.1.involutionCompatible

local notation "rosati" => integralCMRepresentative_integralRosati D C P Z
  compatibility h s hs htor x

variable (T : Over Z.obj.left)

local notation "BT" => Functor.obj (baseChange T.hom) B
local notation "aT" => baseChangeOrderAction T.hom B x.restriction.action
local notation "WT" => (W).pullback P T.hom
local notation "lamT" => (W).pullbackMap P T.hom WT lam

omit [IsCMField F] in
/-- The literal pullback of the original integral action has exactly the original
rational action pulled back along the same structural morphism. -/
theorem integralCMRepresentative_rationalAction_baseChange :
    letI := auxiliaryStarRing D C
    D.harrisHodgePELRationalAction C BT aT =
      (rationalBaseChangeEnd T.hom B).comp x.data.1.actionObj.action := by
  let _ := auxiliaryStarRing D C
  rw [D.harrisHodgePELRationalAction_baseChange, extension_eq]

omit [IsCMField F] in
/-- Every test of the original family has the full actual order equations and
unchanged normalized determinant required by the existing closed action locus. -/
theorem integralCMRepresentative_fullActionCondition :
    letI := auxiliaryStarRing D C
    harrisIntegralCMFullActionCondition D C P Z.obj.hom B W lam T aT := by
  let _ := auxiliaryStarRing D C
  constructor
  · unfold harrisIntegralActionFullRosatiCondition
    have hR := IntegralRosatiEquations.baseChange D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.universality P.compatibility T.hom B x.data.1.hasDual x.data.1.inversePoincare
      x.data.1.evaluation x.data.1.geometry
      (WT).hasDual (WT).inverseBundle (WT).evaluation (WT).geometry rosati
    exact hR
  · rw [integralCMRepresentative_rationalAction_baseChange D C P Z compatibility h s hs htor]
    exact D.harrisTaylorCMRationalLieDeterminantCondition_baseChange_of_naturality C
      Z.obj.hom B x.data.1.actionObj.action T.hom Z.property.lieNaturality x.condition.1

section Classification

variable (R : Over Z.obj.left) [LocallyOfFiniteType R.hom] [IsSeparated R.hom]
  (eR : letI := auxiliaryStarRing D C
    (locallyNoetherianTestInclusion Z.obj.left).op ⋙
      Langlands.GroupScheme.Cartier.relativeHomFunctor
        x.data.1.actionObj.abelianScheme.toCommGroupScheme
        x.data.1.actionObj.abelianScheme.toCommGroupScheme ⋙ forget AddCommGrpCat.{0} ≅
    (locallyNoetherianTestInclusion Z.obj.left).op ⋙ yoneda.obj R)

local notation "locus" => harrisIntegralCMClosedActionLocus D C P Z.obj.hom B W lam R eR
local notation "inc" => harrisIntegralCMClosedActionLocusInclusion D C P Z.obj.hom B W lam R eR
local notation "univAction" => relativeIntegralActionUniversal B
  (D.harrisHodgePELIntegralBasis C) R eR

variable (Q : ObjectProperty.FullSubcategory
  (fun T : Over Z.obj.left => IsLocallyNoetherian T.left))

/-- The original representative, pulled back literally to a test, gives an actual
morphism to the existing closed action locus. -/
def integralCMRepresentative_actionLift :
    letI := auxiliaryStarRing D C
    Q.obj ⟶ locus := by
  let _ := auxiliaryStarRing D C
  exact (harrisIntegralCMClosedActionLocusFullHomEquiv D C P Z.obj.hom B W lam R eR Q).symm
    ⟨baseChangeOrderAction Q.obj.hom B x.restriction.action,
      integralCMRepresentative_fullActionCondition D C P Z compatibility h s hs htor x Q.obj⟩

local notation "liftAt" Q₀:max => integralCMRepresentative_actionLift D C P Z
  compatibility h s hs htor x R eR Q₀

omit [IsCMField F] in
/-- Pulling back the actual universal action along the constructed map recovers
the literal pullback of the original integral action. -/
theorem integralCMRepresentative_actionLift_apply :
    letI := auxiliaryStarRing D C
    (relativeEndRestrict B (liftAt Q ≫ inc)).comp univAction =
      baseChangeOrderAction Q.obj.hom B x.restriction.action := by
  let _ := auxiliaryStarRing D C
  rw [← harrisIntegralCMClosedActionLocusFullHomEquiv_apply]
  exact congrArg Subtype.val
    ((harrisIntegralCMClosedActionLocusFullHomEquiv D C P Z.obj.hom B W lam R eR Q).apply_symm_apply _)

omit [IsCMField F] in
/-- The classifying morphism is uniquely determined by its literal integral action. -/
theorem integralCMRepresentative_actionLift_eq
    (k : letI := auxiliaryStarRing D C; Q.obj ⟶ locus)
    (hk : letI := auxiliaryStarRing D C
      (relativeEndRestrict B (k ≫ inc)).comp univAction =
      baseChangeOrderAction Q.obj.hom B x.restriction.action) :
    k = integralCMRepresentative_actionLift D C P Z compatibility h s hs htor x R eR Q := by
  let _ := auxiliaryStarRing D C
  apply (harrisIntegralCMClosedActionLocusFullHomEquiv D C P Z.obj.hom B W lam R eR Q).injective
  apply Subtype.ext
  rw [harrisIntegralCMClosedActionLocusFullHomEquiv_apply,
    harrisIntegralCMClosedActionLocusFullHomEquiv_apply, hk,
    integralCMRepresentative_actionLift_apply]

omit [IsCMField F] R eR Q in
/-- Relative restriction of the original global integral action agrees with its
direct pullback to the smaller test. -/
theorem integralCMRepresentative_action_restrict {T T' : Over Z.obj.left} (f : T' ⟶ T) :
    letI := auxiliaryStarRing D C
    (relativeEndRestrict B f).comp (baseChangeOrderAction T.hom B x.restriction.action) =
      baseChangeOrderAction T'.hom B x.restriction.action := by
  let _ := auxiliaryStarRing D C
  ext a
  exact Langlands.GroupScheme.Cartier.restrict_baseChange_map
    (AbelianScheme.commHom (x.restriction.action a)) f

omit [IsCMField F] in
/-- The actual classifying maps commute with every morphism of locally
noetherian tests, using the original relative-Hom restriction. -/
theorem integralCMRepresentative_actionLift_naturality
    {Q' : ObjectProperty.FullSubcategory
      (fun T : Over Z.obj.left => IsLocallyNoetherian T.left)}
    (f : Q' ⟶ Q) :
    letI := auxiliaryStarRing D C
    f.hom ≫ liftAt Q = liftAt Q' := by
  let _ := auxiliaryStarRing D C
  apply integralCMRepresentative_actionLift_eq D C P Z compatibility h s hs htor x R eR Q'
  have hv := integralCMRepresentative_actionLift_apply D C P Z
    compatibility h s hs htor x R eR Q
  have hr := integralCMRepresentative_action_restrict D C P Z
    compatibility h s hs htor x f.hom
  rw [← hr, ← hv]
  ext a
  change Langlands.GroupScheme.Cartier.restrict (B).toCommGroupScheme (B).toCommGroupScheme
      ((f.hom ≫ liftAt Q) ≫ inc) (univAction a) =
    Langlands.GroupScheme.Cartier.restrict (B).toCommGroupScheme (B).toCommGroupScheme f.hom
      (Langlands.GroupScheme.Cartier.restrict (B).toCommGroupScheme (B).toCommGroupScheme
        (liftAt Q ≫ inc) (univAction a))
  rw [Category.assoc]
  exact Langlands.GroupScheme.Cartier.restrict_comp (B).toCommGroupScheme
    (B).toCommGroupScheme f.hom (liftAt Q ≫ inc) (univAction a)

end Classification

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
