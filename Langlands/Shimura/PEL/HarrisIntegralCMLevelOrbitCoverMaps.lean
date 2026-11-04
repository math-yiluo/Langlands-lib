import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCovers

/-! # Maps of finite-etale Harris monodromy orbit covers -/

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

/-- Lift an actual finite orbit action morphism to a morphism of its actual covers. -/
def harrisIntegralCMFiniteOrbitCoverMap
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      (orbitAction U V hU q ⟶ orbitAction U Z hU r) →
      (orbitCover U V hU q ⟶ orbitCover U Z hU r) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  letI : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro q r f
  exact (continuousActionFunctor s hs).inv.map f

local notation "coverMap" =>
  harrisIntegralCMFiniteOrbitCoverMap
    D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The cover map has the prescribed actual action on geometric fibres. -/
theorem harrisIntegralCMFiniteOrbitCoverMap_action
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z)
      (f : orbitAction U V hU q ⟶ orbitAction U Z hU r),
      (continuousActionFunctor s hs).map (coverMap U V Z hU q r f) =
        (orbitIso U V hU q).hom ≫ f ≫ (orbitIso U Z hU r).inv := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro q r f
  exact (continuousActionFunctor s hs).map_preimage _

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual fibre-action comparisons are natural for the lifted maps. -/
theorem harrisIntegralCMFiniteOrbitCoverMap_naturality
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z)
      (f : orbitAction U V hU q ⟶ orbitAction U Z hU r),
      (continuousActionFunctor s hs).map (coverMap U V Z hU q r f) ≫
        (orbitIso U Z hU r).hom = (orbitIso U V hU q).hom ≫ f := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r f
  rw [harrisIntegralCMFiniteOrbitCoverMap_action]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On actual geometric lifts the comparison carries postcomposition to the raw map. -/
theorem harrisIntegralCMFiniteOrbitCoverMap_fiber
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z)
      (f : orbitAction U V hU q ⟶ orbitAction U Z hU r)
      (x : Fiber s (orbitCover U V hU q)),
      fiberEquiv U Z hU r (x ≫ (coverMap U V Z hU q r f).hom) =
        f.hom.hom (fiberEquiv U V hU q x) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r f x
  have heq := harrisIntegralCMFiniteOrbitCoverMap_naturality
    D C P B W lam T a compatibility h s hs htor hu U V Z hU q r f
  exact congrArg (fun k : (continuousActionFunctor s hs).obj (orbitCover U V hU q) ⟶
    orbitAction U Z hU r => k.hom.hom x) heq

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Lifting the identity action morphism gives the identity cover morphism. -/
theorem harrisIntegralCMFiniteOrbitCoverMap_id
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, coverMap U V V hU q q (𝟙 _) = 𝟙 (orbitCover U V hU q) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro q
  exact (continuousActionFunctor s hs).inv.map_id _

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Lifting a composite action morphism gives the composite actual cover morphism. -/
theorem harrisIntegralCMFiniteOrbitCoverMap_comp
    (U V Z J : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (t : RawOrbits J)
      (f : orbitAction U V hU q ⟶ orbitAction U Z hU r)
      (g : orbitAction U Z hU r ⟶ orbitAction U J hU t),
      coverMap U V J hU q t (f ≫ g) =
        coverMap U V Z hU q r f ≫ coverMap U Z J hU r t g := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro q r t f g
  exact (continuousActionFunctor s hs).inv.map_comp f g

local notation "levelArrow" => (hodgeLevelFunctor D C).map
local notation "transport" f =>
  RightOrbit.translate (levelArrow f).element (levelArrow f).respects

/-- The original Harris transporter restricts to a morphism of actual finite orbit actions.
The target class is its prescribed raw image. -/
def harrisIntegralCMFiniteOrbitTransportActionMap
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) (f : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z), (transport f) q = r →
      (orbitAction U V hU q ⟶ orbitAction U Z hU r) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr
  refine ObjectProperty.homMk { hom := FintypeCat.homMk (fun x => ?_), comm := ?_ }
  · refine ⟨(transport f) x.val, ?_⟩
    obtain ⟨gamma, hgamma⟩ := x.property
    refine ⟨gamma, ?_⟩
    change gamma • r = (transport f) x.val
    calc
      gamma • r = gamma • (transport f) q := congrArg (fun z => gamma • z) hqr.symm
      _ = (transport f) (gamma • q) :=
        (RightOrbit.translate_smul (levelArrow f).element (levelArrow f).respects gamma q).symm
      _ = (transport f) x.val := congrArg (transport f) hgamma
  · intro gamma
    apply FintypeCat.hom_ext
    intro x
    apply Subtype.ext
    exact RightOrbit.translate_smul (levelArrow f).element (levelArrow f).respects gamma x.val

local notation "transportActionMap" => harrisIntegralCMFiniteOrbitTransportActionMap
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω] in
/-- Identity transport gives the identity on the actual finite orbit action. -/
theorem harrisIntegralCMFiniteOrbitTransportActionMap_id
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (hqq : (transport (𝟙 V)) q = q),
      transportActionMap U V V hU (𝟙 V) q q hqq = 𝟙 (orbitAction U V hU q) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q hqq
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro x
  apply Subtype.ext
  change (transport (𝟙 V)) x.val = x.val
  rw [(hodgeLevelFunctor D C).map_id]
  exact RightOrbit.translate_one x.val

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω] in
/-- Composition of original Harris transporters gives composition of finite orbit maps. -/
theorem harrisIntegralCMFiniteOrbitTransportActionMap_comp
    (U V Z J : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U))
    (f : V ⟶ Z) (g : Z ⟶ J) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (t : RawOrbits J)
      (hqr : (transport f) q = r) (hrt : (transport g) r = t)
      (hqt : (transport (f ≫ g)) q = t),
      transportActionMap U V J hU (f ≫ g) q t hqt =
        transportActionMap U V Z hU f q r hqr ≫ transportActionMap U Z J hU g r t hrt := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r t hqr hrt hqt
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro x
  apply Subtype.ext
  change (transport (f ≫ g)) x.val = (transport g) ((transport f) x.val)
  rw [(hodgeLevelFunctor D C).map_comp]
  exact (RightOrbit.translate_comp (levelArrow f).element (levelArrow g).element
    (levelArrow f).respects (levelArrow g).respects x.val).symm

/-- The original Harris transporter gives an actual morphism of the finite-etale orbit covers. -/
def harrisIntegralCMFiniteOrbitCoverTransport
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) (f : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z), (transport f) q = r →
      (orbitCover U V hU q ⟶ orbitCover U Z hU r) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr
  exact coverMap U V Z hU q r (transportActionMap U V Z hU f q r hqr)

local notation "coverTransport" => harrisIntegralCMFiniteOrbitCoverTransport
  D C P B W lam T a compatibility h s hs htor hu
local notation "coverPoint" => harrisIntegralCMFiniteOrbitCoverPoint
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual cover transporter acts on fibres by the original raw Harris translation. -/
theorem harrisIntegralCMFiniteOrbitCoverTransport_fiber
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) (f : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport f) q = r)
      (x : Fiber s (orbitCover U V hU q)),
      (fiberEquiv U Z hU r (x ≫ (coverTransport U V Z hU f q r hqr).hom)).val =
        (transport f) (fiberEquiv U V hU q x).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr x
  exact congrArg Subtype.val (harrisIntegralCMFiniteOrbitCoverMap_fiber
    D C P B W lam T a compatibility h s hs htor hu U V Z hU q r
    (transportActionMap U V Z hU f q r hqr) x)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual transporter carries the distinguished geometric lift to its prescribed lift. -/
theorem harrisIntegralCMFiniteOrbitCoverTransport_point
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) (f : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport f) q = r),
      coverPoint U V hU q ≫ (coverTransport U V Z hU f q r hqr).hom =
        coverPoint U Z hU r := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr
  apply (fiberEquiv U Z hU r).injective
  apply Subtype.ext
  rw [harrisIntegralCMFiniteOrbitCoverTransport_fiber,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_point,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_point]
  exact hqr

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Identity transport gives the identity morphism on the actual cover. -/
theorem harrisIntegralCMFiniteOrbitCoverTransport_id
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (hqq : (transport (𝟙 V)) q = q),
      coverTransport U V V hU (𝟙 V) q q hqq = 𝟙 (orbitCover U V hU q) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q hqq
  unfold harrisIntegralCMFiniteOrbitCoverTransport
  rw [harrisIntegralCMFiniteOrbitTransportActionMap_id]
  exact harrisIntegralCMFiniteOrbitCoverMap_id
    D C P B W lam T a compatibility h s hs htor hu U V hU q

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Composition of original Harris transporters gives composition of actual cover morphisms. -/
theorem harrisIntegralCMFiniteOrbitCoverTransport_comp
    (U V Z J : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U))
    (f : V ⟶ Z) (g : Z ⟶ J) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (t : RawOrbits J)
      (hqr : (transport f) q = r) (hrt : (transport g) r = t)
      (hqt : (transport (f ≫ g)) q = t),
      coverTransport U V J hU (f ≫ g) q t hqt =
        coverTransport U V Z hU f q r hqr ≫ coverTransport U Z J hU g r t hrt := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r t hqr hrt hqt
  unfold harrisIntegralCMFiniteOrbitCoverTransport
  rw [harrisIntegralCMFiniteOrbitTransportActionMap_comp
    D C P B W lam T a compatibility h s hs htor hu U V Z J hU f g q r t hqr hrt hqt]
  exact harrisIntegralCMFiniteOrbitCoverMap_comp
    D C P B W lam T a compatibility h s hs htor hu U V Z J hU q r t _ _

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
