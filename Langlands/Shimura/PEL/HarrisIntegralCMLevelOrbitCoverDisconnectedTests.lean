import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverTestNaturality
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentCoproduct

/-! # Original Harris orbit-cover levels on disconnected tests -/

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

open scoped FintypeCatDiscrete

/-- An actual connected open component, with the original structural map. -/
abbrev harrisIntegralCMComponentTest {S : Scheme.{0}} (X : Over S)
    [IsLocallyNoetherian X.left] (c : _root_.ConnectedComponents X.left) : Over S :=
  Over.mk (Langlands.AlgebraicGeometry.componentι X.left c ≫ X.hom)

/-- The actual open-component inclusion as a morphism over the original base. -/
abbrev harrisIntegralCMComponentTestInclusion {S : Scheme.{0}} (X : Over S)
    [IsLocallyNoetherian X.left] (c : _root_.ConnectedComponents X.left) :
    harrisIntegralCMComponentTest X c ⟶ X :=
  Over.homMk (Langlands.AlgebraicGeometry.componentι X.left c) rfl

open Langlands.AlgebraicGeometry

/-- Actual morphisms over a fixed target glue uniquely from the actual open
connected components of the source. -/
def harrisIntegralCMComponentHomEquiv {S : Scheme.{0}} {X T : Over S}
    [IsLocallyNoetherian X.left] (f : X ⟶ T) (Y : Over T.left) :
    (Over.mk f.left ⟶ Y) ≃
      (∀ c : _root_.ConnectedComponents X.left,
        Over.mk ((harrisIntegralCMComponentTestInclusion X c ≫ f).left) ⟶ Y) where
  toFun k c :=
    (Over.homMk (componentι X.left c) rfl :
      Over.mk ((harrisIntegralCMComponentTestInclusion X c ≫ f).left) ⟶
        Over.mk f.left) ≫ k
  invFun k := Over.homMk (componentDesc X.left (fun c => (k c).left)) (by
    apply component_hom_ext X.left
    intro c
    rw [← Category.assoc, componentι_componentDesc]
    exact Over.w (k c))
  left_inv k := by
    apply Over.OverMorphism.ext
    exact componentDesc_restrict X.left k.left
  right_inv k := by
    funext c
    apply Over.OverMorphism.ext
    exact componentι_componentDesc X.left (fun d => (k d).left) c

@[simp] theorem harrisIntegralCMComponentHomEquiv_apply {S : Scheme.{0}} {X T : Over S}
    [IsLocallyNoetherian X.left] (f : X ⟶ T) (Y : Over T.left)
    (k : Over.mk f.left ⟶ Y) (c : _root_.ConnectedComponents X.left) :
    harrisIntegralCMComponentHomEquiv f Y k c =
      (Over.homMk (componentι X.left c) rfl :
        Over.mk ((harrisIntegralCMComponentTestInclusion X c ≫ f).left) ⟶
          Over.mk f.left) ≫ k := rfl

@[simp] theorem harrisIntegralCMComponentHomEquiv_symm_left
    {S : Scheme.{0}} {X T : Over S} [IsLocallyNoetherian X.left]
    (f : X ⟶ T) (Y : Over T.left)
    (k : ∀ c : _root_.ConnectedComponents X.left,
      Over.mk ((harrisIntegralCMComponentTestInclusion X c ≫ f).left) ⟶ Y) :
    ((harrisIntegralCMComponentHomEquiv f Y).symm k).left =
      componentDesc X.left (fun c => (k c).left) := rfl

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
local notation "H" =>
  ScalarExtensionSimilitudePoints A A (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "Frame" => harrisIntegralCMWeilFrame D C P B W lam T a compatibility h s
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

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]

open scoped FintypeCatDiscrete

local notation "orbitCover" =>
  harrisIntegralCMFiniteOrbitCover D C P B W lam T a compatibility h s hs htor hu
local notation "fiberEquiv" =>
  harrisIntegralCMFiniteOrbitCoverFiberEquiv
    D C P B W lam T a compatibility h s hs htor hu
local notation "rawTower" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h s hs htor hu


variable {X : Over S} [IsLocallyNoetherian X.left]
    (f : X ⟶ T)

local notation "Xc" c:max => harrisIntegralCMComponentTest X c
local notation "inc" c:max => harrisIntegralCMComponentTestInclusion X c
local notation "fc" c:max => inc c ≫ f

local instance componentTestConnected (c : _root_.ConnectedComponents X.left) :
    ConnectedSpace (harrisIntegralCMComponentTest X c).left :=
  componentSchemeConnected X.left c

local instance componentTestLocallyNoetherian (c : _root_.ConnectedComponents X.left) :
    IsLocallyNoetherian (harrisIntegralCMComponentTest X c).left :=
  componentSchemeLocallyNoetherian X.left c

local instance componentTestQuasiSeparated (c : _root_.ConnectedComponents X.left) :
    QuasiSeparatedSpace (harrisIntegralCMComponentTest X c).left :=
  inferInstanceAs (QuasiSeparatedSpace (componentScheme X.left c))

variable
    (t : ∀ c : _root_.ConnectedComponents X.left,
      Spec (.of Ω) ⟶ componentScheme X.left c)
    (es : ∀ c, t c ≫ (harrisIntegralCMComponentTestInclusion X c ≫ f).left = s)
    (ht : ∀ c, ∀ Y : Cover (componentScheme X.left c), Finite (Fiber (t c) Y))
    (huC : ∀ c, ∀ k : Index (fun _ => True),
      IsUnit (k.val : Γ(componentScheme X.left c, ⊤)))
    [hμfinC : ∀ c, ∀ k : Index (fun _ => True),
      IsFinite (mu (componentScheme X.left c) k.val).X.hom]
    [hμetC : ∀ c, ∀ k : Index (fun _ => True),
      Etale (mu (componentScheme X.left c) k.val).X.hom]

local instance componentMuFinite (c : _root_.ConnectedComponents X.left) :
    ∀ k : Index (fun _ => True),
      IsFinite (mu (harrisIntegralCMComponentTest X c).left k.val).X.hom :=
  hμfinC c

local instance componentMuEtale (c : _root_.ConnectedComponents X.left) :
    ∀ k : Index (fun _ => True),
      Etale (mu (harrisIntegralCMComponentTest X c).left k.val).X.hom :=
  hμetC c

local notation "rawC" c:max => harrisIntegralCMFullActionLevelTower
  D C P B W lam (Xc c) ((relativeEndRestrict B (fc c)).comp a)
    compatibility h (t c) (ht c) htor (huC c)
local notation "evalC" c:max => harrisIntegralCMRestrictionRawClass
  D C P B W lam (fc c) a compatibility h (t c) (ht c) htor (huC c) s (es c) hs
local notation "testEquivC" c:max => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor hu
    (fc c) (t c) (es c) (ht c) (huC c)

/-- On an arbitrary locally noetherian test with supplied compatible component
points, actual maps into the orbit cover correspond to the product of original
direct-level orbit subtypes on its actual connected open components. -/
def harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      (Over.mk f.left ⟶ (orbitCover U V hU q).obj) ≃
        (∀ c : _root_.ConnectedComponents X.left,
          {l : (rawC c).obj V // (evalC c) V l ∈ MulAction.orbit Gamma q}) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  exact (harrisIntegralCMComponentHomEquiv f (orbitCover U V hU q).obj).trans
    (Equiv.piCongrRight (fun c => (testEquivC c) U V hU q))

local notation "disconnectedEquiv" =>
  harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv
    D C P B W lam T a compatibility h s hs htor hu f t es ht huC

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Its component value is the original connected-test correspondence applied
to the actual restriction of the scheme map. -/
theorem harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv_component
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj)
      (c : _root_.ConnectedComponents X.left),
      disconnectedEquiv U V hU q k c =
        (testEquivC c) U V hU q
          ((Over.homMk (componentι X.left c) rfl :
            Over.mk (fc c).left ⟶ Over.mk f.left) ≫ k) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q k c
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The inverse is the actual gluing of the inverse connected correspondences. -/
theorem harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv_symm_left
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V)
      (l : ∀ c : _root_.ConnectedComponents X.left,
        {l : (rawC c).obj V // (evalC c) V l ∈ MulAction.orbit Gamma q}),
      ((disconnectedEquiv U V hU q).symm l).left =
        componentDesc X.left (fun c => ((testEquivC c) U V hU q).symm (l c) |>.left) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q l
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original raw evaluation on a component is the actual scheme-map value at
its supplied point, followed by the constructed geometric-fibre comparison. -/
theorem harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv_val
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj)
      (c : _root_.ConnectedComponents X.left),
      (evalC c) V (disconnectedEquiv U V hU q k c).val =
        (fiberEquiv U V hU q
          (Over.homMk (t c ≫ (componentι X.left c ≫ k.left)) (by
            rw [Category.assoc, Category.assoc, Over.w k]
            exact es c))).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q k c
  exact harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val
    D C P B W lam T a compatibility h s hs htor hu
      (fc c) (t c) (es c) (ht c) (huC c) U V hU q
      ((Over.homMk (componentι X.left c) rfl :
        Over.mk (fc c).left ⟶ Over.mk f.left) ≫ k)

local notation "levelArrow" => (hodgeLevelFunctor D C).map
local notation "transport" j:max =>
  RightOrbit.translate (levelArrow j).element (levelArrow j).respects
local notation "coverTransport" => harrisIntegralCMFiniteOrbitCoverTransport
  D C P B W lam T a compatibility h s hs htor hu
local notation "testMapC" c:max => harrisIntegralCMTestLevelOrbitMap
  D C P B W lam T a compatibility h s hs htor hu
    (fc c) (t c) (es c) (ht c) (huC c)

/-- The component product transition uses each original direct tower map. -/
def harrisIntegralCMDisconnectedTestLevelOrbitMap
    {V Z : HarrisLevel D} (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z), (transport j) q = r →
      (∀ c : _root_.ConnectedComponents X.left,
        {l : (rawC c).obj V // (evalC c) V l ∈ MulAction.orbit Gamma q}) →
      (∀ c : _root_.ConnectedComponents X.left,
        {l : (rawC c).obj Z // (evalC c) Z l ∈ MulAction.orbit Gamma r}) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr l c
  exact (testMapC c) j q r hqr (l c)

local notation "disconnectedMap" => harrisIntegralCMDisconnectedTestLevelOrbitMap
  D C P B W lam T a compatibility h s hs htor hu f t es ht huC

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω] in
/-- On each component, the product transition is literally the original direct
tower transition. -/
theorem harrisIntegralCMDisconnectedTestLevelOrbitMap_val
    {V Z : HarrisLevel D} (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r)
      (l : ∀ c : _root_.ConnectedComponents X.left,
        {l : (rawC c).obj V // (evalC c) V l ∈ MulAction.orbit Gamma q})
      (c : _root_.ConnectedComponents X.left),
      (disconnectedMap j q r hqr l c).val = (rawC c).map j (l c).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr l c
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual cover transporter postcomposition agrees with the product of the
original direct level transitions on every actual source component. -/
theorem harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv_natural
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r)
      (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj),
      disconnectedMap j q r hqr (disconnectedEquiv U V hU q k) =
        disconnectedEquiv U Z hU r
          (k ≫ (coverTransport U V Z hU j q r hqr).hom) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr k
  funext c
  exact harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_natural
    D C P B W lam T a compatibility h s hs htor hu
      (fc c) (t c) (es c) (ht c) (huC c) U V Z hU j q r hqr
      ((Over.homMk (componentι X.left c) rfl :
        Over.mk (fc c).left ⟶ Over.mk f.left) ≫ k)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
