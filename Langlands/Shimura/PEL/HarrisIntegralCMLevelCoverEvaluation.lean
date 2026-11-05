import Langlands.Shimura.PEL.HarrisIntegralCMLevelImageFixedEquivalence
import Langlands.GroupTheory.TransitiveActionEvaluation

/-! # Restricted raw levels from equivariant finite-etale fibre maps -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

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
    {S : Scheme.{0}} (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)
    {T T' : Over S} [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
    (f : T' ⟶ T) [IsFinite f.left] [Etale f.left]
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ T.left)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (x : Fiber s (cover f.left))
    (ht : ∀ Y : Cover T'.left, Finite (Fiber x.left Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "H" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "Gamma" => FundamentalGroup s hs
local notation "Frame" => harrisIntegralCMWeilFrame
  D C P B W lam T a compatibility h s
local notation "rightAction" => Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) s
local notation "monodromyAction" => Tate.weilAdelicFrameMonodromyAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  compatibility rationalWeilGeometricTransport (WT).hasDual (WT).geometry
  (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) s hs htor huT
local notation "actionsComm" => Tate.weilAdelicFrameActionsComm P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  compatibility rationalWeilGeometricTransport (WT).hasDual (WT).geometry
  (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) s hs htor huT
local notation "rawD" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T' ((relativeEndRestrict B f).comp a) compatibility h x.left ht htor huD
local notation "levelSubgroup" V => ((hodgeLevelFunctor D C).obj V).subgroup
local notation "imageEquiv" => harrisIntegralCMRestrictionImageFixedEquivAt
  D C P B W lam f a compatibility h x.left ht htor huT huD s (Over.w x) hs
local notation "rawEvaluation" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h x.left ht htor huD s (Over.w x) hs

/-- An actual equivariant fibre map gives a fixed level on the direct family
with the literal restricted integral action. -/
def harrisIntegralCMCoverFiberMapLevel (V : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    (Fiber s (cover f.left) →[Gamma] RightOrbit Frame (levelSubgroup V)) →
      (rawD).obj V := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro k
  refine (imageEquiv V).symm ⟨k x, ?_⟩
  intro g
  have hx : fundamentalGroupMap f.left x.left s (Over.w x) ht hs g • x = x :=
    fundamentalGroupMap_fixes_lift s hs (cover f.left) x ht g
  exact (k.map_smul _ _).symm.trans (congrArg k hx)

local notation "ofFiberMap" => harrisIntegralCMCoverFiberMapLevel
  D C P B W lam f a compatibility h s hs x ht htor huT huD

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Evaluating the resulting direct raw level returns the original map's
literal value at the chosen lift. -/
theorem harrisIntegralCMCoverFiberMapLevel_val (V : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ k : Fiber s (cover f.left) →[Gamma] RightOrbit Frame (levelSubgroup V),
      rawEvaluation V (ofFiberMap V k) = k x := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro k
  rw [← harrisIntegralCMRestrictionImageFixedEquivAt_apply_val
    D C P B W lam f a compatibility h x.left ht htor huT huD s (Over.w x) hs]
  exact congrArg Subtype.val ((imageEquiv V).apply_symm_apply _)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- For a transitive actual fibre action, distinct equivariant maps yield
distinct direct restricted raw levels. -/
theorem harrisIntegralCMCoverFiberMapLevel_injective (V : HarrisLevel D)
    [MulAction.IsPretransitive Gamma (Fiber s (cover f.left))] :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    Function.Injective (ofFiberMap V) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro k l he
  apply Langlands.GroupTheory.equivariantMap_evaluation_injective x
  have hv := congrArg (rawEvaluation V) he
  simpa only [harrisIntegralCMCoverFiberMapLevel_val] using hv

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
