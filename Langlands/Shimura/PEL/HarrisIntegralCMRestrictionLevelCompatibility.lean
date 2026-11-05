import Langlands.Shimura.PEL.HarrisIntegralCMLevelImageFixedEquivalence

/-! # Level-arrow compatibility of actual raw restriction evaluation -/

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

section ImageFixedPullback

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
    (f : T' ⟶ T)
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "BD" => (AbelianScheme.baseChange T'.hom).obj B
local notation "BC" => (AbelianScheme.baseChange f.left).obj BT
local notation "WT" => W.pullback P T.hom
local notation "WD" => W.pullback P T'.hom
local notation "WC" => (WT).pullback P f.left
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "lamD" => W.pullbackMap P T'.hom WD lam
local notation "lamC" => canonicalDualValuedBaseChange f.left BT P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.universality (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation lamT
local notation "aD" => (relativeEndRestrict B f).comp a
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "iD" => D.harrisHodgePELRationalAction C BD aD
local notation "iC" => (rationalBaseChangeEnd f.left BT).comp iT
local notation "e" => relativeIntegralActionRationalComparisonIso B
  (D.harrisHodgePELIntegralBasis C) f a
local notation "addDC" => relativeDualSchemeMapAdditivity P.preservation P.stability
  T'.left BD BC (WD).hasDual (WC).hasDual

variable
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T'.left)
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (hs : ∀ Y : Cover T.left, Finite (Fiber (t ≫ f.left) Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "rawT" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h (t ≫ f.left) hs htor huT
local notation "rawD" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T' aD compatibility h t ht htor huD
local notation "rawC" => hodgeLevelFunctor D C ⋙
  Tate.weilAdelicCompactOpenLevelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation lamC
    h iC A (D.harrisHodgePELForm C) t ht htor huD

local notation "FrameT" => harrisIntegralCMWeilFrame
  D C P B W lam T a compatibility h (t ≫ f.left)
local notation "FrameC" => Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamC
  h iC A (D.harrisHodgePELForm C) t
local notation "HT" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "HC" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "GammaT" => FundamentalGroup (t ≫ f.left) hs
local notation "GammaD" => FundamentalGroup t ht
local notation "rightT" => Tate.weilAdelicFrameRightAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) (t ≫ f.left)
local notation "monT" => Tate.weilAdelicFrameMonodromyAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (WT).hasDual (WT).geometry (WT).inverseBundle
  (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) (t ≫ f.left) hs htor huT
local notation "commT" => Tate.weilAdelicFrameActionsComm P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (WT).hasDual (WT).geometry (WT).inverseBundle
  (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) (t ≫ f.left) hs htor huT
local notation "rightC" => Tate.weilAdelicFrameRightAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamC
  h iC A (D.harrisHodgePELForm C) t
local notation "monC" => Tate.weilAdelicFrameMonodromyAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (WC).hasDual (WC).geometry (WC).inverseBundle
  (WC).evaluation lamC h iC A (D.harrisHodgePELForm C) t ht htor huD
local notation "commC" => Tate.weilAdelicFrameActionsComm P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (WC).hasDual (WC).geometry (WC).inverseBundle
  (WC).evaluation lamC h iC A (D.harrisHodgePELForm C) t ht htor huD
local notation "frameBC" => Tate.weilAdelicFrameBaseChange f.left BT P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.universality (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) t
local notation "frameRight" => Tate.weilAdelicFrameBaseChange_right f.left BT P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.universality (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) t
local notation "orbitBC" => Tate.weilAdelicFrameRightOrbitBaseChange f.left BT P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.universality (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) t
local notation "frameMon" => Tate.weilAdelicFrameBaseChange_monodromy f.left BT P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.universality (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) t ht hs htor huT huD
local notation "alpha" => fundamentalGroupMap f.left t (t ≫ f.left) rfl ht hs
local notation "compare" => harrisIntegralCMFullActionRestrictionLevelIso
  D C P B W lam f a compatibility h t ht htor huD
local notation "levelSubgroup" V => ((hodgeLevelFunctor D C).obj V).subgroup

section PointEquality

variable (s : Spec (.of Ω) ⟶ T.left) (es : t ≫ f.left = s)
  (hs0 : ∀ Y : Cover T.left, Finite (Fiber s Y))

local notation "FrameS" => harrisIntegralCMWeilFrame
  D C P B W lam T a compatibility h s
local notation "rightS" => Tate.weilAdelicFrameRightAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) s
local notation "monS" => Tate.weilAdelicFrameMonodromyAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (WT).hasDual (WT).geometry (WT).inverseBundle
  (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) s hs0 htor huT
local notation "commS" => Tate.weilAdelicFrameActionsComm P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability compatibility
  rationalWeilGeometricTransport (WT).hasDual (WT).geometry (WT).inverseBundle
  (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) s hs0 htor huT
local notation "alphaS" => fundamentalGroupMap f.left t s es ht hs0

local notation "levelArrow" => (hodgeLevelFunctor D C).map

omit [IsCMField F] [IsScalarTower ℚ F A] hμfinT hμetT in
/-- Actual restriction evaluation commutes with every original Harris level arrow. -/
theorem harrisIntegralCMRestrictionRawClass_map
    {V Z : HarrisLevel D} (j : V ⟶ Z) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    ∀ r : (rawD).obj V,
      harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        t ht htor huD s es hs0 Z ((rawD).map j r) =
      RightOrbit.translate (levelArrow j).element (levelArrow j).respects
        (harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
          t ht htor huD s es hs0 V r) := by
  subst s
  let : MulAction HTᵐᵒᵖ FrameT := rightT
  let : MulAction HCᵐᵒᵖ FrameT := rightT
  let : MulAction HTᵐᵒᵖ FrameC := rightC
  let : MulAction HCᵐᵒᵖ FrameC := rightC
  intro r
  have hn : (compare).hom.app Z ((rawD).map j r) =
      (rawC).map j ((compare).hom.app V r) :=
    ConcreteCategory.congr_hom ((compare).hom.naturality j) r
  change (orbitBC (levelSubgroup Z))
      ((compare).hom.app Z ((rawD).map j r)).val = _
  rw [hn]
  exact Tate.weilAdelicFrameRightOrbitBaseChange_translate f.left BT P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability P.universality (WT).hasDual (WT).geometry (WT).inverseBundle
    (WT).evaluation (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation
    compatibility lamT h iT A (D.harrisHodgePELForm C) t
    (levelArrow j).element (levelArrow j).respects ((compare).hom.app V r).val

end PointEquality

end ImageFixedPullback

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
