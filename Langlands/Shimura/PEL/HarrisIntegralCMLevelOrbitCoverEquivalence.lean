import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverRangeNaturality
import Langlands.AlgebraicGeometry.FiniteEtale.CoverStabilizerLift

/-! # Direct level equivalence for selected finite-etale orbit covers -/

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


local notation "homLevelRangeEquiv" => harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω] in
/-- Restriction of an actual direct fixed level to the original geometric
point is fixed by the full stabilizer of the chosen lift to a finite-etale cover. -/
theorem harrisIntegralCMCoverRestrictionRawClass_stabilizer_fixed
    (Y : Cover T.left) (x : Fiber s Y) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
    let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
    ∀ [QuasiSeparatedSpace Tq.left]
      (ht : ∀ K : Cover Y.obj.left, Finite (Fiber x.left K))
      (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
      [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
      [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom]
      (Z : HarrisLevel D)
      (l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
        ((relativeEndRestrict B fq).comp a)
        compatibility h x.left ht htor huY).obj Z)
      (g : Gamma), g • x = x →
      g • harrisIntegralCMRestrictionRawClass D C P B W lam fq a
        compatibility h x.left ht htor huY s (Over.w x) hs Z l =
      harrisIntegralCMRestrictionRawClass D C P B W lam fq a
        compatibility h x.left ht htor huY s (Over.w x) hs Z l := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro instQS ht huY instMuFin instMuEt Z l g hg
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  let e := harrisIntegralCMRestrictionImageFixedEquivAt D C P B W lam fq a
    compatibility h x.left ht htor hu huY s (Over.w x) hs Z
  have hx := (e l).property (stabilizerLift s hs Y x ht g hg)
  change fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs
    (stabilizerLift s hs Y x ht g hg) • (e l).val = (e l).val at hx
  rw [fundamentalGroupMap_stabilizerLift] at hx
  have he := harrisIntegralCMRestrictionImageFixedEquivAt_apply_val
    D C P B W lam fq a compatibility h x.left ht htor hu huY s (Over.w x) hs Z l
  change (e l).val = _ at he
  rw [he] at hx
  exact hx

/-- Actual morphisms between selected covers are exactly the direct fixed
levels whose original raw evaluation belongs to the target monodromy orbit. -/
def harrisIntegralCMFiniteOrbitCoverHomLevelEquiv
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ K : Cover Y.obj.left, Finite (Fiber x.left K))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        (Y ⟶ orbitCover U Z hU r) ≃
          {l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
              ((relativeEndRestrict B fq).comp a)
              compatibility h x.left ht htor huY).obj Z //
            harrisIntegralCMRestrictionRawClass D C P B W lam fq a
              compatibility h x.left ht htor huY s (Over.w x) hs Z l ∈
                MulAction.orbit Gamma r} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  letI : QuasiSeparatedSpace Tq.left := instQS
  letI : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  letI : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  refine (homLevelRangeEquiv U V Z hU q r ht huY).trans
    { toFun := fun l => ⟨l.val, l.property.1⟩
      invFun := fun l => ⟨l.val, l.property, ?_⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact harrisIntegralCMCoverRestrictionRawClass_stabilizer_fixed
    D C P B W lam T a compatibility h s hs htor hu Y x ht huY Z l.val

local notation "homLevelEquiv" => harrisIntegralCMFiniteOrbitCoverHomLevelEquiv
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The simplified equivalence retains the original Hom-to-direct-level map. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevelEquiv_apply_val
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ K : Cover Y.obj.left, Finite (Fiber x.left K))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom]
        (f : Y ⟶ orbitCover U Z hU r),
        (homLevelEquiv U V Z hU q r ht huY f).val =
          homLevel U V Z hU q r ht huY f := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt f
  rfl

/-- The actual Harris tower transition preserves target-orbit membership
on direct fixed levels, constructed through the actual cover transporter. -/
def harrisIntegralCMFiniteOrbitCoverHomLevelMap
    (U V Z J : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : Z ⟶ J) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (t : RawOrbits J)
      (_hrt : (transport j) r = t),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ K : Cover Y.obj.left, Finite (Fiber x.left K))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        {l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
            ((relativeEndRestrict B fq).comp a)
            compatibility h x.left ht htor huY).obj Z //
          let z := harrisIntegralCMRestrictionRawClass D C P B W lam fq a
            compatibility h x.left ht htor huY s (Over.w x) hs Z l
          z ∈ MulAction.orbit Gamma r} →
        {l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
            ((relativeEndRestrict B fq).comp a)
            compatibility h x.left ht htor huY).obj J //
          let z := harrisIntegralCMRestrictionRawClass D C P B W lam fq a
            compatibility h x.left ht htor huY s (Over.w x) hs J l
          z ∈ MulAction.orbit Gamma t} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r t hrt instQS ht huY instMuFin instMuEt l
  let Y := orbitCover U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  letI : QuasiSeparatedSpace Tq.left := instQS
  letI : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  letI : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  exact homLevelEquiv U V J hU q t ht huY
    ((homLevelEquiv U V Z hU q r ht huY).symm l ≫
      coverTransport U Z J hU j r t hrt)

local notation "levelMap" => harrisIntegralCMFiniteOrbitCoverHomLevelMap
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The map between orbit-condition subtypes has the original direct raw
tower map as its underlying function. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevelMap_val
    (U V Z J : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : Z ⟶ J) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (t : RawOrbits J)
      (hrt : (transport j) r = t),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ K : Cover Y.obj.left, Finite (Fiber x.left K))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom]
        (l : {l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
            ((relativeEndRestrict B fq).comp a)
            compatibility h x.left ht htor huY).obj Z //
          let z := harrisIntegralCMRestrictionRawClass D C P B W lam fq a
            compatibility h x.left ht htor huY s (Over.w x) hs Z l
          z ∈ MulAction.orbit Gamma r}),
        (levelMap U V Z J hU j q r t hrt ht huY l).val =
          (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
            ((relativeEndRestrict B fq).comp a)
            compatibility h x.left ht htor huY).map j l.val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r t hrt instQS ht huY instMuFin instMuEt l
  let Y := orbitCover U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  let eZ := homLevelEquiv U V Z hU q r ht huY
  change homLevel U V J hU q t ht huY
    (eZ.symm l ≫ coverTransport U Z J hU j r t hrt) = _
  rw [harrisIntegralCMFiniteOrbitCoverHomLevel_postcomp_transport]
  have he : homLevel U V Z hU q r ht huY (eZ.symm l) = l.val :=
    congrArg Subtype.val (eZ.apply_symm_apply l)
  rw [he]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The direct level equivalence intertwines postcomposition by the actual
cover transporter with the original direct tower transition. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevelEquiv_natural
    (U V Z J : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : Z ⟶ J) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (t : RawOrbits J)
      (hrt : (transport j) r = t),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ K : Cover Y.obj.left, Finite (Fiber x.left K))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom]
        (f : Y ⟶ orbitCover U Z hU r),
        levelMap U V Z J hU j q r t hrt ht huY
            (homLevelEquiv U V Z hU q r ht huY f) =
          homLevelEquiv U V J hU q t ht huY
            (f ≫ coverTransport U Z J hU j r t hrt) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r t hrt instQS ht huY instMuFin instMuEt f
  let Y := orbitCover U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  let eZ := homLevelEquiv U V Z hU q r ht huY
  let eJ := homLevelEquiv U V J hU q t ht huY
  change eJ (eZ.symm (eZ f) ≫ coverTransport U Z J hU j r t hrt) =
    eJ (f ≫ coverTransport U Z J hU j r t hrt)
  rw [eZ.symm_apply_apply]


end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
