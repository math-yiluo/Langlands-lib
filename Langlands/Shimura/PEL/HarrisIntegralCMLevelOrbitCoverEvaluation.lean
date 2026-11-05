import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitUniversalProperty
import Langlands.Shimura.PEL.HarrisIntegralCMLevelCoverEvaluation

/-! # Restricted raw levels associated with actual orbit-cover morphisms -/

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

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual geometric fibre of a selected orbit cover is pretransitive. -/
theorem harrisIntegralCMFiniteOrbitCoverFiber_pretransitive
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      MulAction.IsPretransitive Gamma (Fiber s (orbitCover U V hU q)) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Gamma)
    (fiberEquiv U V hU q x) (fiberEquiv U V hU q y)
  refine ⟨g, (fiberEquiv U V hU q).injective ?_⟩
  exact (harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul
    D C P B W lam T a compatibility h s hs htor hu U V hU q g x).trans hg

/-- A morphism into the selected cover gives an actual equivariant map into
the full old raw quotient, by including its finite monodromy orbit. -/
def harrisIntegralCMFiniteOrbitCoverHomRawMap
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left),
      (Y ⟶ orbitCover U V hU q) → (Fiber s Y →[Gamma] RawOrbits V) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y f
  refine
    { toFun := fun x => (fiberEquiv U V hU q (x ≫ f.hom)).val
      map_smul' := ?_ }
  intro g x
  exact congrArg Subtype.val
    (ConcreteCategory.congr_hom ((homEquiv U V hU q Y f).hom.comm g) x)

local notation "homRawMap" => harrisIntegralCMFiniteOrbitCoverHomRawMap
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The underlying map uses literal postcomposition on geometric lifts. -/
theorem harrisIntegralCMFiniteOrbitCoverHomRawMap_apply
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left) (f : Y ⟶ orbitCover U V hU q)
      (x : Fiber s Y),
      homRawMap U V hU q Y f x = (fiberEquiv U V hU q (x ≫ f.hom)).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y f x
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Passing from cover morphisms to full raw-valued equivariant maps is injective. -/
theorem harrisIntegralCMFiniteOrbitCoverHomRawMap_injective
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left),
      Function.Injective (homRawMap U V hU q Y) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y f g he
  apply (homEquiv U V hU q Y).injective
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro x
  apply Subtype.ext
  exact congrArg (fun k : Fiber s Y →[Gamma] RawOrbits V => k x) he

/-- A morphism between selected orbit covers gives a fixed raw level on the
direct source family with its literal restricted integral action. -/
def harrisIntegralCMFiniteOrbitCoverHomLevel
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  letI : IsFinite fq.left := Y.property.1
  letI : Etale fq.left := Y.property.2
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        (Y ⟶ orbitCover U Z hU r) →
          (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
            ((relativeEndRestrict B fq).comp a)
            compatibility h x.left ht htor huY).obj Z := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt f
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  letI : IsFinite fq.left := Y.property.1
  letI : Etale fq.left := Y.property.2
  letI : QuasiSeparatedSpace Tq.left := instQS
  letI : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  letI : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  exact harrisIntegralCMCoverFiberMapLevel D C P B W lam fq a compatibility h
    s hs x ht htor hu huY Z (homRawMap U Z hU r Y f)

local notation "homLevel" => harrisIntegralCMFiniteOrbitCoverHomLevel
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Restriction evaluation of the resulting direct level is exactly the raw
value of postcomposing the distinguished source lift with the cover morphism. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevel_val
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    let : MulAction Hᵐᵒᵖ Frame := rightAction
    let : MulAction Gamma Frame := monodromyAction
    let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : IsFinite fq.left := Y.property.1
  let : Etale fq.left := Y.property.2
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom]
        (f : Y ⟶ orbitCover U Z hU r),
        harrisIntegralCMRestrictionRawClass D C P B W lam fq a compatibility h
          x.left ht htor huY s (Over.w x) hs Z
          (homLevel U V Z hU q r ht huY f) =
            (fiberEquiv U Z hU r (x ≫ f.hom)).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt f
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : IsFinite fq.left := Y.property.1
  let : Etale fq.left := Y.property.2
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  exact harrisIntegralCMCoverFiberMapLevel_val D C P B W lam fq a compatibility h
    s hs x ht htor hu huY Z (homRawMap U Z hU r Y f)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- A selected source orbit cover's direct raw level determines the actual
cover morphism that gave it; source-fibre transitivity is proved internally. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevel_injective
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    let : MulAction Hᵐᵒᵖ Frame := rightAction
    let : MulAction Gamma Frame := monodromyAction
    let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        Function.Injective (homLevel U V Z hU q r ht huY) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt f g he
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : IsFinite fq.left := Y.property.1
  let : Etale fq.left := Y.property.2
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  let : MulAction.IsPretransitive Gamma (Fiber s (cover fq.left)) :=
    harrisIntegralCMFiniteOrbitCoverFiber_pretransitive
      D C P B W lam T a compatibility h s hs htor hu U V hU q
  apply harrisIntegralCMFiniteOrbitCoverHomRawMap_injective
    D C P B W lam T a compatibility h s hs htor hu U Z hU r Y
  exact harrisIntegralCMCoverFiberMapLevel_injective
    D C P B W lam fq a compatibility h s hs x ht htor hu huY Z he

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
