import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverEvaluation
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverMaps
import Langlands.Shimura.PEL.HarrisIntegralCMRestrictionLevelCompatibility

/-! # Identity and transporter compatibility of actual orbit-cover levels -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
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
    (T : Over S) [QuasiSeparatedSpace T.left]
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ T.left)

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "H" =>
  ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

local notation "Frame" => harrisIntegralCMWeilFrame D C P B W lam T a compatibility h s
local notation "coord" => harrisIntegralCMFrameEquiv D C P B W lam T a compatibility h s
local notation "cosetEquiv" => harrisIntegralCMFrameCosetEquiv
  D C P B W lam T a compatibility h s
local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).subgroup
local notation "RawOrbits" U => RightOrbit Frame (levelSubgroup U)
local notation "rightAction" =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) s

variable
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "Gamma" => FundamentalGroup s hs

local notation "monodromyAction" =>
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C)
    s hs htor hu

local notation "actionsComm" =>
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C)
    s hs htor hu

local notation "rho" => harrisIntegralCMFrameMonodromy
  D C P B W lam T a compatibility h s hs htor hu

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]

open scoped FintypeCatDiscrete

local notation "orbitAction" =>
  harrisIntegralCMFiniteOrbitAction D C P B W lam T a compatibility h s hs htor hu
local notation "orbitCover" =>
  harrisIntegralCMFiniteOrbitCover D C P B W lam T a compatibility h s hs htor hu
local notation "orbitIso" =>
  harrisIntegralCMFiniteOrbitCoverActionIso
    D C P B W lam T a compatibility h s hs htor hu
local notation "fiberEquiv" =>
  harrisIntegralCMFiniteOrbitCoverFiberEquiv
    D C P B W lam T a compatibility h s hs htor hu

local notation "rawTower" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h s hs htor hu
local notation "coverPoint" => harrisIntegralCMFiniteOrbitCoverPoint
  D C P B W lam T a compatibility h s hs htor hu
local notation "homEquiv" => harrisIntegralCMFiniteOrbitCoverHomEquiv
  D C P B W lam T a compatibility h s hs htor hu

local notation "homLevel" => harrisIntegralCMFiniteOrbitCoverHomLevel
  D C P B W lam T a compatibility h s hs htor hu
local notation "coverLevel" => harrisIntegralCMFiniteOrbitCoverLevel
  D C P B W lam T a compatibility h s hs htor hu
local notation "levelArrow" => (hodgeLevelFunctor D C).map
local notation "transport" j =>
  RightOrbit.translate (levelArrow j).element (levelArrow j).respects
local notation "coverTransport" => harrisIntegralCMFiniteOrbitCoverTransport
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The identity cover morphism recovers the selected cover's original direct level. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevel_id
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        homLevel U V V hU q q ht huY (𝟙 Y) = coverLevel U V hU q ht huY := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q instQS ht huY instMuFin instMuEt
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : IsFinite fq.left := Y.property.1
  let : Etale fq.left := Y.property.2
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  apply harrisIntegralCMRestrictionRawClass_injective
    D C P B W lam fq a compatibility h x.left ht htor huY s (Over.w x) hs V
  rw [harrisIntegralCMFiniteOrbitCoverHomLevel_val,
    harrisIntegralCMFiniteOrbitCoverLevel_val]
  change (fiberEquiv U V hU q x).val = q
  exact harrisIntegralCMFiniteOrbitCoverFiberEquiv_point
    D C P B W lam T a compatibility h s hs htor hu U V hU q

/-- A Harris transporter gives a direct restricted level through its actual
morphism between the selected orbit covers. -/
def harrisIntegralCMFiniteOrbitCoverTransportLevel
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (_hqr : (transport j) q = r),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
          ((relativeEndRestrict B fq).comp a)
          compatibility h x.left ht htor huY).obj Z := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r hqr instQS ht huY instMuFin instMuEt
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  letI : IsFinite fq.left := Y.property.1
  letI : Etale fq.left := Y.property.2
  letI : QuasiSeparatedSpace Tq.left := instQS
  letI : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  letI : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  exact homLevel U V Z hU q r ht huY (coverTransport U V Z hU j q r hqr)

local notation "transportLevel" => harrisIntegralCMFiniteOrbitCoverTransportLevel
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Evaluation of the transporter-induced direct level recovers the exact
prescribed target raw class. -/
theorem harrisIntegralCMFiniteOrbitCoverTransportLevel_val
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        harrisIntegralCMRestrictionRawClass D C P B W lam fq a compatibility h
          x.left ht htor huY s (Over.w x) hs Z
          (transportLevel U V Z hU j q r hqr ht huY) = r := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r hqr instQS ht huY instMuFin instMuEt
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : IsFinite fq.left := Y.property.1
  let : Etale fq.left := Y.property.2
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  change harrisIntegralCMRestrictionRawClass D C P B W lam fq a compatibility h
    x.left ht htor huY s (Over.w x) hs Z
    (homLevel U V Z hU q r ht huY (coverTransport U V Z hU j q r hqr)) = r
  rw [harrisIntegralCMFiniteOrbitCoverHomLevel_val,
    harrisIntegralCMFiniteOrbitCoverTransport_point,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_point]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The transporter-induced direct level equals the actual transition in the
original direct raw level tower on the selected source cover. -/
theorem harrisIntegralCMFiniteOrbitCoverTransportLevel_eq_map
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        transportLevel U V Z hU j q r hqr ht huY =
          (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
            ((relativeEndRestrict B fq).comp a)
            compatibility h x.left ht htor huY).map j
            (coverLevel U V hU q ht huY) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r hqr instQS ht huY instMuFin instMuEt
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : IsFinite fq.left := Y.property.1
  let : Etale fq.left := Y.property.2
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  apply harrisIntegralCMRestrictionRawClass_injective
    D C P B W lam fq a compatibility h x.left ht htor huY s (Over.w x) hs Z
  rw [harrisIntegralCMFiniteOrbitCoverTransportLevel_val,
    harrisIntegralCMRestrictionRawClass_map,
    harrisIntegralCMFiniteOrbitCoverLevel_val]
  exact hqr.symm

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
