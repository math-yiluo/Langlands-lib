import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverTestEquivalence
import Langlands.Shimura.PEL.HarrisIntegralCMRestrictionLevelCompatibility
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverMaps

/-! # Level naturality on arbitrary connected tests of Harris orbit covers -/

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

variable {T' : Over S} [QuasiSeparatedSpace T'.left]
    [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left]
    (f : T' ⟶ T) (t : Spec (.of Ω) ⟶ T'.left) (es : t ≫ f.left = s)
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))

local notation "alpha" => fundamentalGroupMap f.left t s es ht hs

variable
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "rawD" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T' ((relativeEndRestrict B f).comp a)
    compatibility h t ht htor huD
local notation "rawEvaluation" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h t ht htor huD s es hs

local notation "testLevelEquiv" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor hu f t es ht huD
local notation "levelArrow" => (hodgeLevelFunctor D C).map
local notation "transport" j =>
  RightOrbit.translate (levelArrow j).element (levelArrow j).respects
local notation "coverTransport" => harrisIntegralCMFiniteOrbitCoverTransport
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On arbitrary connected tests, actual transporter postcomposition agrees
with the original direct level-tower transition. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_postcomp_transport
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r)
      (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj),
      (testLevelEquiv U Z hU r
        (k ≫ (coverTransport U V Z hU j q r hqr).hom)).val =
      (rawD).map j (testLevelEquiv U V hU q k).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr k
  apply harrisIntegralCMRestrictionRawClass_injective
    D C P B W lam f a compatibility h t ht htor huD s es hs Z
  rw [harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val,
    harrisIntegralCMRestrictionRawClass_map,
    harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val]
  let x : Fiber s (orbitCover U V hU q) :=
    Over.homMk (t ≫ k.left) (by rw [Category.assoc, Over.w k]; exact es)
  exact harrisIntegralCMFiniteOrbitCoverTransport_fiber
    D C P B W lam T a compatibility h s hs htor hu U V Z hU j q r hqr x

/-- The original direct tower transition preserves target-orbit values on
an arbitrary connected test. -/
def harrisIntegralCMTestLevelOrbitMap
    {V Z : HarrisLevel D} (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z), (transport j) q = r →
      {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q} →
      {l : (rawD).obj Z // rawEvaluation Z l ∈ MulAction.orbit Gamma r} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr l
  refine ⟨(rawD).map j l.val, ?_⟩
  rw [harrisIntegralCMRestrictionRawClass_map]
  obtain ⟨g, hg⟩ := l.property
  refine ⟨g, ?_⟩
  change g • r = (transport j) (rawEvaluation V l.val)
  calc
    g • r = g • (transport j) q := congrArg (fun z => g • z) hqr.symm
    _ = (transport j) (g • q) :=
      (RightOrbit.translate_smul (levelArrow j).element
        (levelArrow j).respects g q).symm
    _ = (transport j) (rawEvaluation V l.val) := congrArg (transport j) hg

local notation "testLevelMap" => harrisIntegralCMTestLevelOrbitMap
  D C P B W lam T a compatibility h s hs htor hu f t es ht huD

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]
  [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left] in
/-- The subtype transition is literally the original direct level transition. -/
theorem harrisIntegralCMTestLevelOrbitMap_val
    {V Z : HarrisLevel D} (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r)
      (l : {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q}),
      (testLevelMap j q r hqr l).val = (rawD).map j l.val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr l
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]
  [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left] in
/-- Identity level transport induces the identity on the orbit-valued levels. -/
theorem harrisIntegralCMTestLevelOrbitMap_id
    (V : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (hqq : (transport (𝟙 V)) q = q)
      (l : {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q}),
      testLevelMap (𝟙 V) q q hqq l = l := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q hqq l
  apply Subtype.ext
  exact ConcreteCategory.congr_hom ((rawD).map_id V) l.val

omit [IsCMField F] [IsScalarTower ℚ F A]
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]
  [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left] in
/-- Composition of original level arrows induces composition on the
orbit-valued direct levels. -/
theorem harrisIntegralCMTestLevelOrbitMap_comp
    {V Z J : HarrisLevel D} (j : V ⟶ Z) (k : Z ⟶ J) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (z : RawOrbits J)
      (hqr : (transport j) q = r) (hrz : (transport k) r = z)
      (hqz : (transport (j ≫ k)) q = z)
      (l : {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q}),
      testLevelMap (j ≫ k) q z hqz l =
        testLevelMap k r z hrz (testLevelMap j q r hqr l) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r z hqr hrz hqz l
  apply Subtype.ext
  exact ConcreteCategory.congr_hom ((rawD).map_comp j k) l.val

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The arbitrary-test equivalence intertwines actual transporter
postcomposition with the original direct-level transition on the orbit subtype. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_natural
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) (j : V ⟶ Z) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (hqr : (transport j) q = r)
      (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj),
      testLevelMap j q r hqr (testLevelEquiv U V hU q k) =
        testLevelEquiv U Z hU r
          (k ≫ (coverTransport U V Z hU j q r hqr).hom) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr k
  apply Subtype.ext
  exact (harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_postcomp_transport
    D C P B W lam T a compatibility h s hs htor hu f t es ht huD
      U V Z hU j q r hqr k).symm

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
