import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCovers
import Langlands.Shimura.PEL.HarrisIntegralCMLevelRestriction
import Langlands.AlgebraicGeometry.FiniteEtale.CoverPointStabilizer

/-! # Actual raw levels on the selected Harris orbit covers -/

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

/-- A raw orbit fixed by the image of the new fundamental group is an actual
fixed level on the successively pulled-back family. -/
def harrisIntegralCMImageFixedSuccessiveLevel (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    ∀ q : RightOrbit FrameT (levelSubgroup V),
      (∀ g : GammaD, alpha g • q = q) → (rawC).obj V := by
  letI : MulAction HTᵐᵒᵖ FrameT := rightT
  letI : MulAction GammaT FrameT := monT
  letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
  letI : MulAction HTᵐᵒᵖ FrameC := rightC
  letI : MulAction GammaD FrameC := monC
  letI : SMulCommClass GammaD HTᵐᵒᵖ FrameC := commC
  letI : MulAction HCᵐᵒᵖ FrameT := rightT
  letI : SMulCommClass GammaT HCᵐᵒᵖ FrameT := commT
  letI : MulAction HCᵐᵒᵖ FrameC := rightC
  letI : SMulCommClass GammaD HCᵐᵒᵖ FrameC := commC
  intro q hq
  refine ⟨(orbitBC (levelSubgroup V)).symm q, ?_⟩
  intro g
  apply (orbitBC (levelSubgroup V)).injective
  change RightOrbit.map (X := FrameC) (Y := FrameT) (levelSubgroup V) frameBC frameRight
      (g • (orbitBC (levelSubgroup V)).symm q) =
    RightOrbit.map (X := FrameC) (Y := FrameT) (levelSubgroup V) frameBC frameRight
      ((orbitBC (levelSubgroup V)).symm q)
  rw [RightOrbit.map_smul (X := FrameC) (Y := FrameT) (levelSubgroup V) alpha frameBC frameRight frameMon]
  change alpha g • ((orbitBC (levelSubgroup V)) ((orbitBC (levelSubgroup V)).symm q)) =
    (orbitBC (levelSubgroup V)) ((orbitBC (levelSubgroup V)).symm q)
  rw [Equiv.apply_symm_apply]
  exact hq g

/-- Transfer the image-fixed class to the original direct pullback, whose
integral action is literally relativeEndRestrict of the supplied action. -/
def harrisIntegralCMImageFixedLevel (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    ∀ q : RightOrbit FrameT (levelSubgroup V),
      (∀ g : GammaD, alpha g • q = q) → (rawD).obj V := by
  letI : MulAction HTᵐᵒᵖ FrameT := rightT
  letI : MulAction GammaT FrameT := monT
  letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
  intro q hq
  exact (compare).inv.app V
    (harrisIntegralCMImageFixedSuccessiveLevel
      D C P B W lam f a compatibility h t ht hs htor huT huD V q hq)

local notation "successive" => harrisIntegralCMImageFixedSuccessiveLevel
  D C P B W lam f a compatibility h t ht hs htor huT huD
local notation "direct" => harrisIntegralCMImageFixedLevel
  D C P B W lam f a compatibility h t ht hs htor huT huD

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The successive fixed level has exactly the inverse base-changed raw class. -/
@[simp] theorem harrisIntegralCMImageFixedSuccessiveLevel_val (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    ∀ (q : RightOrbit FrameT (levelSubgroup V))
      (hq : ∀ g : GammaD, alpha g • q = q),
      (successive V q hq).val = (orbitBC (levelSubgroup V)).symm q := by
  intro q hq
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Comparing the direct output with the successive family recovers exactly
that same inverse base-changed raw class. -/
theorem harrisIntegralCMImageFixedLevel_compare (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    ∀ (q : RightOrbit FrameT (levelSubgroup V))
      (hq : ∀ g : GammaD, alpha g • q = q),
      ((compare).hom.app V (direct V q hq)).val =
        (orbitBC (levelSubgroup V)).symm q := by
  intro q hq
  change ((compare).hom.app V ((compare).inv.app V (successive V q hq))).val = _
  have he := congrArg (fun k => k (successive V q hq))
    (NatTrans.congr_app (compare).inv_hom_id V)
  exact (congrArg Subtype.val he).trans rfl

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

/-- Evaluate a direct restricted level back in the original raw orbit set,
retaining a propositional equality of the geometric points. -/
def harrisIntegralCMRestrictionRawClass (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    (rawD).obj V → RightOrbit FrameS (levelSubgroup V) := by
  subst s
  intro r
  exact (orbitBC (levelSubgroup V)) ((compare).hom.app V r).val

/-- Image-fixed pullback also applies when the pointed base-change equation
is propositional rather than definitional. -/
def harrisIntegralCMImageFixedLevelAt (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    letI : MulAction (FundamentalGroup s hs0) FrameS := monS
    letI : SMulCommClass (FundamentalGroup s hs0) HTᵐᵒᵖ FrameS := commS
    ∀ q : RightOrbit FrameS (levelSubgroup V),
      (∀ g : GammaD, alphaS g • q = q) → (rawD).obj V := by
  subst s
  exact harrisIntegralCMImageFixedLevel
    D C P B W lam f a compatibility h t ht hs0 htor huT huD V

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Evaluation of the resulting direct level returns the exact original class. -/
theorem harrisIntegralCMImageFixedLevelAt_val (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    letI : MulAction (FundamentalGroup s hs0) FrameS := monS
    letI : SMulCommClass (FundamentalGroup s hs0) HTᵐᵒᵖ FrameS := commS
    ∀ (q : RightOrbit FrameS (levelSubgroup V))
      (hq : ∀ g : GammaD, alphaS g • q = q),
      harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        t ht htor huD s es hs0 V
        (harrisIntegralCMImageFixedLevelAt D C P B W lam f a compatibility h
          t ht htor huT huD s es hs0 V q hq) = q := by
  subst s
  intro q hq
  change (orbitBC (levelSubgroup V))
    (((compare).hom.app V
      (harrisIntegralCMImageFixedLevel
        D C P B W lam f a compatibility h t ht hs0 htor huT huD V q hq)).val) = q
  rw [harrisIntegralCMImageFixedLevel_compare]
  exact Equiv.apply_symm_apply _ _

end PointEquality

end ImageFixedPullback

section SelectedCover

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

local notation "rawTower" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h s hs htor hu
local notation "selectedCover" => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h s hs htor hu
local notation "selectedPoint" => harrisIntegralCMFiniteOrbitCoverPoint
  D C P B W lam T a compatibility h s hs htor hu
local notation "fiberEquiv" => harrisIntegralCMFiniteOrbitCoverFiberEquiv
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The fundamental group of the selected orbit cover, at its distinguished
lift, maps into the stabilizer of the exact original raw class. -/
theorem harrisIntegralCMFiniteOrbitCover_image_fixes
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      let Y := selectedCover U V hU q
      let x := selectedPoint U V hU q
      ∀ (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
        (g : FundamentalGroup x.left ht),
        fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs g • q = q := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q ht g
  let Y := selectedCover U V hU q
  let x := selectedPoint U V hU q
  let alpha := fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs
  have hx : alpha g • x = x := fundamentalGroupMap_fixes_lift s hs Y x ht g
  have he := congrArg Subtype.val
    (harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul
      D C P B W lam T a compatibility h s hs htor hu U V hU q (alpha g) x)
  change (fiberEquiv U V hU q (alpha g • x)).val =
    alpha g • (fiberEquiv U V hU q x).val at he
  rw [hx, harrisIntegralCMFiniteOrbitCoverFiberEquiv_point] at he
  exact he.symm

/-- The class defining the selected orbit cover becomes a fixed level on the
direct pullback of the original family, with its restricted integral action. -/
def harrisIntegralCMFiniteOrbitCoverLevel
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      let Y := selectedCover U V hU q
      let x := selectedPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
          ((relativeEndRestrict B fq).comp a)
          compatibility h x.left ht htor huY).obj V := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q instQS ht huY instMuFin instMuEt
  let Y := selectedCover U V hU q
  let x := selectedPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  letI : QuasiSeparatedSpace Tq.left := instQS
  letI : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  letI : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  exact harrisIntegralCMImageFixedLevelAt D C P B W lam fq a compatibility h
    x.left ht htor hu huY s (Over.w x) hs V q
    (harrisIntegralCMFiniteOrbitCover_image_fixes
      D C P B W lam T a compatibility h s hs htor hu U V hU q ht)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Evaluation of the selected cover's direct fixed level recovers its exact
defining class at the original geometric point. -/
theorem harrisIntegralCMFiniteOrbitCoverLevel_val
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      let Y := selectedCover U V hU q
      let x := selectedPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        harrisIntegralCMRestrictionRawClass D C P B W lam fq a compatibility h
          x.left ht htor huY s (Over.w x) hs V
          (harrisIntegralCMFiniteOrbitCoverLevel D C P B W lam T a compatibility h
            s hs htor hu U V hU q ht huY) = q := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q instQS ht huY instMuFin instMuEt
  let Y := selectedCover U V hU q
  let x := selectedPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  let : QuasiSeparatedSpace Tq.left := instQS
  let : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  let : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  exact harrisIntegralCMImageFixedLevelAt_val D C P B W lam fq a compatibility h
    x.left ht htor hu huY s (Over.w x) hs V q
    (harrisIntegralCMFiniteOrbitCover_image_fixes
      D C P B W lam T a compatibility h s hs htor hu U V hU q ht)

end SelectedCover

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
