import Langlands.Shimura.PEL.HarrisCMWeilTower
import Langlands.Shimura.PEL.HarrisTaylorCMActionPresheaf

/-! # The joint CM action class underlying the actual Harris Weil tower -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

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
  {S : Scheme.{0}} (p : S ⟶ Spec (.of F))

local notation "PositiveObject" => PositivePolarizedAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (S := S)
local notation "Condition" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p
local notation "Level" => HarrisLevel D

/-- On the same actual positive polarized object, central trace is redundant once
the normalized determinant and prescribed geometric dimension hold. -/
theorem objectCondition_iff_determinantDimension (X : PositiveObject) :
    Condition X ↔
      letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C p
        X.actionObj.abelianScheme X.actionObj.action := by
  let := auxiliaryStarRing D C
  exact (D.harrisTaylorCMDeterminantDimensionCondition_iff C p
    X.actionObj.abelianScheme X.actionObj.action).symm

variable
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Classes" => IsoClass D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality p compatibility h s hs htor hu additivity
local notation "mkClass" => classOf D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality p compatibility h s hs htor hu additivity
local notation "mapClass" => classMap D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality p compatibility h s hs htor hu additivity
local notation "tower" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity
local notation "forgetNum" => forgetNumericalAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity
local notation "JointClass" => D.HarrisTaylorCMActionClass C p

/-- Forget the polarization and Weil level using one representative satisfying
both the normalized determinant and the actual geometric dimension. -/
def forgetCMAction {U : Level} (q : Classes U) : JointClass := by
  letI := auxiliaryStarRing D C
  refine ⟨(forgetNum q).val, ?_⟩
  obtain ⟨x, hx, hq⟩ := classOf_surjective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p
    compatibility h s hs htor hu additivity q
  rw [← hq]
  exact ⟨x.1.actionObj, rfl,
    (objectCondition_iff_determinantDimension D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality p x.1).mp hx⟩

local notation "forgetCM" => forgetCMAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h
  s hs htor hu additivity

@[simp] theorem forgetCMAction_val {U : Level} (q : Classes U) :
    (forgetCM q).val = (forgetNum q).val := rfl

@[simp] theorem forgetCMAction_classOf {U : Level} (x : Data U) (hx : Condition x.1) :
    letI := auxiliaryStarRing D C
    forgetCM (mkClass x hx) =
      D.harrisTaylorCMActionClassOf C p x.1.actionObj
        ((objectCondition_iff_determinantDimension D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality p x.1).mp hx) := rfl

/-- Every genuine original-Harris level arrow retains the same joint action class. -/
theorem forgetCMAction_classMap {U V : Level} (f : U ⟶ V) (q : Classes U) :
    forgetCM (mapClass f q) = forgetCM q := by
  apply Subtype.ext
  change (forgetNum (mapClass f q)).val = (forgetNum q).val
  exact congrArg (fun z : HarrisTaylor.NumericalActionClass L F p n E (A := A) => z.val)
    (forgetNumericalAction_classMap D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h
      s hs htor hu additivity f q)

/-- The joint action classes receive a natural transformation from the actual tower. -/
def forgetCMActionNatTrans : tower ⟶ (Functor.const Level).obj JointClass where
  app _ := ↾forgetCM
  naturality {U V} f := by
    ext q
    exact forgetCMAction_classMap D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h
      s hs htor hu additivity f q

/-- The joint forgetful map retains precisely the previous numerical action image. -/
theorem forgetCMAction_toNumerical {U : Level} (q : Classes U) :
    (⟨(forgetCM q).val,
      ((D.harrisTaylorCMActionClassCondition_iff C p (forgetCM q).val).mp
        (forgetCM q).property).2⟩ :
      HarrisTaylor.NumericalActionClass L F p n E (A := A)) = forgetNum q :=
  Subtype.ext rfl

/-- Forgetting a compact-open subgroup does not change the joint action class. -/
theorem forgetCMAction_forgetLevel {U V : Level} (hU : U.subgroup ≤ V.subgroup)
    (q : Classes U) :
    forgetCM
      (forgetLevel D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality p compatibility h s hs htor hu additivity hU q) =
      forgetCM q :=
  forgetCMAction_classMap D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p compatibility h
    s hs htor hu additivity (CompactOpenLevel.inclusion hU) q

include D C in
omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem actionProjectionRationalFinite : Module.Finite ℚ A :=
  (hodgeRationalPELConditions D C).finite_module

local notation "OriginalGroup" =>
  D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

/-- The inclusion leg of every actual Hecke correspondence retains the joint class. -/
theorem forgetCMAction_heckeLeft (U V : Level) (g : OriginalGroup)
    (q : letI := actionProjectionRationalFinite D C
      Classes (CompactOpenLevel.heckeLevel U V g)) :
    letI := actionProjectionRationalFinite D C
    forgetCM
      (heckeLeft D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality p compatibility h s hs htor hu additivity
        U V g q) = forgetCM q := by
  let := actionProjectionRationalFinite D C
  exact forgetCMAction_classMap D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p compatibility h
    s hs htor hu additivity (CompactOpenLevel.heckeLeft U V g) q

/-- The translation leg from that same Hecke intersection retains the same joint class. -/
theorem forgetCMAction_heckeRight (U V : Level) (g : OriginalGroup)
    (q : letI := actionProjectionRationalFinite D C
      Classes (CompactOpenLevel.heckeLevel U V g)) :
    letI := actionProjectionRationalFinite D C
    forgetCM
      (heckeRight D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality p compatibility h s hs htor hu additivity
        U V g q) = forgetCM q := by
  let := actionProjectionRationalFinite D C
  exact forgetCMAction_classMap D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality p compatibility h
    s hs htor hu additivity (CompactOpenLevel.heckeRight U V g) q

/-- Pulling back the forgotten joint class uses the actual pulled-back action on
the same representative; this does not assert pullback of its polarization or level. -/
theorem forgetCMAction_presheaf_map_classOf_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {T : Scheme.{0}} (f : T ⟶ S) {U : Level} (x : Data U) (hx : Condition x.1) :
    letI := auxiliaryStarRing D C
    ((D.harrisTaylorCMActionPresheaf C allNaturality).map
      (Over.homMk f rfl : Over.mk (f ≫ p) ⟶ Over.mk p).op
      (forgetCM (mkClass x hx))).val =
        RationalAlgebraAction.classOf ((RationalAlgebraAction.pullback f).obj x.1.actionObj) := rfl

end Langlands.Shimura.PEL.HarrisCMWeilLevel
