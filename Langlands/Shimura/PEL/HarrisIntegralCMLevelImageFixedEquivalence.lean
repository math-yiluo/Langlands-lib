import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverLevels

/-! # Direct restricted levels and image-fixed raw classes -/

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

/-- Evaluate a direct restricted level as an old raw class fixed by the
image of the new fundamental group. -/
def harrisIntegralCMRestrictionImageFixedClass (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    (rawD).obj V → {q : RightOrbit FrameT (levelSubgroup V) //
      ∀ g : GammaD, alpha g • q = q} := by
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
  intro r
  let c := (compare).hom.app V r
  refine ⟨(orbitBC (levelSubgroup V)) c.val, ?_⟩
  intro g
  change alpha g • RightOrbit.map (X := FrameC) (Y := FrameT)
      (levelSubgroup V) frameBC frameRight c.val =
    RightOrbit.map (X := FrameC) (Y := FrameT)
      (levelSubgroup V) frameBC frameRight c.val
  rw [← RightOrbit.map_smul (X := FrameC) (Y := FrameT)
    (levelSubgroup V) alpha frameBC frameRight frameMon]
  rw [c.property g]

local notation "evaluate" => harrisIntegralCMRestrictionImageFixedClass
  D C P B W lam f a compatibility h t ht hs htor huT huD
local notation "direct" => harrisIntegralCMImageFixedLevel
  D C P B W lam f a compatibility h t ht hs htor huT huD
local notation "successive" => harrisIntegralCMImageFixedSuccessiveLevel
  D C P B W lam f a compatibility h t ht hs htor huT huD

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The image-fixed evaluation has the existing pointed restriction value. -/
theorem harrisIntegralCMRestrictionImageFixedClass_val (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    ∀ r : (rawD).obj V,
      (evaluate V r).val =
        harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
          t ht htor huD (t ≫ f.left) rfl hs V r := by
  intro r
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Pulling back the evaluated class returns the original direct level. -/
theorem harrisIntegralCMImageFixedLevel_evaluate (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    ∀ r : (rawD).obj V,
      direct V (evaluate V r).val (evaluate V r).property = r := by
  let : MulAction HTᵐᵒᵖ FrameT := rightT
  let : MulAction GammaT FrameT := monT
  let : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
  intro r
  have hc : successive V (evaluate V r).val (evaluate V r).property =
      (compare).hom.app V r := by
    apply Subtype.ext
    change (orbitBC (levelSubgroup V)).symm
      ((orbitBC (levelSubgroup V)) ((compare).hom.app V r).val) = _
    exact Equiv.symm_apply_apply _ _
  change (compare).inv.app V
    (successive V (evaluate V r).val (evaluate V r).property) = r
  rw [hc]
  exact congrArg (fun k => k r) (NatTrans.congr_app (compare).hom_inv_id V)

/-- Direct fixed levels are exactly the old raw classes fixed by the image of
the new fundamental group, via the actual pointed Weil comparison. -/
def harrisIntegralCMRestrictionImageFixedEquiv (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameT := rightT
    letI : MulAction GammaT FrameT := monT
    letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
    (rawD).obj V ≃ {q : RightOrbit FrameT (levelSubgroup V) //
      ∀ g : GammaD, alpha g • q = q} := by
  letI : MulAction HTᵐᵒᵖ FrameT := rightT
  letI : MulAction GammaT FrameT := monT
  letI : SMulCommClass GammaT HTᵐᵒᵖ FrameT := commT
  refine
    { toFun := evaluate V
      invFun := fun q => direct V q.val q.property
      left_inv := harrisIntegralCMImageFixedLevel_evaluate
        D C P B W lam f a compatibility h t ht hs htor huT huD V
      right_inv := ?_ }
  intro q
  apply Subtype.ext
  rw [harrisIntegralCMRestrictionImageFixedClass_val]
  exact harrisIntegralCMImageFixedLevelAt_val D C P B W lam f a compatibility h
    t ht htor huT huD (t ≫ f.left) rfl hs V q.val q.property

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

/-- The direct-level/image-invariant equivalence retains an arbitrary old
geometric point and its propositional compatibility equation. -/
def harrisIntegralCMRestrictionImageFixedEquivAt (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    letI : MulAction (FundamentalGroup s hs0) FrameS := monS
    letI : SMulCommClass (FundamentalGroup s hs0) HTᵐᵒᵖ FrameS := commS
    (rawD).obj V ≃ {q : RightOrbit FrameS (levelSubgroup V) //
      ∀ g : GammaD, alphaS g • q = q} := by
  subst s
  exact harrisIntegralCMRestrictionImageFixedEquiv
    D C P B W lam f a compatibility h t ht hs0 htor huT huD V

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The equivalence evaluates by the existing actual restriction comparison. -/
theorem harrisIntegralCMRestrictionImageFixedEquivAt_apply_val
    (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    letI : MulAction (FundamentalGroup s hs0) FrameS := monS
    letI : SMulCommClass (FundamentalGroup s hs0) HTᵐᵒᵖ FrameS := commS
    ∀ r : (rawD).obj V,
      (harrisIntegralCMRestrictionImageFixedEquivAt D C P B W lam f a
        compatibility h t ht htor huT huD s es hs0 V r).val =
      harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        t ht htor huD s es hs0 V r := by
  subst s
  intro r
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The inverse equivalence is the previous actual image-fixed pullback. -/
theorem harrisIntegralCMRestrictionImageFixedEquivAt_symm_apply
    (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    letI : MulAction (FundamentalGroup s hs0) FrameS := monS
    letI : SMulCommClass (FundamentalGroup s hs0) HTᵐᵒᵖ FrameS := commS
    ∀ q : {q : RightOrbit FrameS (levelSubgroup V) //
        ∀ g : GammaD, alphaS g • q = q},
      (harrisIntegralCMRestrictionImageFixedEquivAt D C P B W lam f a
        compatibility h t ht htor huT huD s es hs0 V).symm q =
      harrisIntegralCMImageFixedLevelAt D C P B W lam f a compatibility h
        t ht htor huT huD s es hs0 V q.val q.property := by
  subst s
  intro q
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] hμfinT hμetT in
/-- The old raw evaluation uniquely determines the direct restricted level. -/
theorem harrisIntegralCMRestrictionRawClass_injective (V : HarrisLevel D) :
    letI : MulAction HTᵐᵒᵖ FrameS := rightS
    Function.Injective
      (harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        t ht htor huD s es hs0 V) := by
  let : MulAction HTᵐᵒᵖ FrameS := rightS
  subst s
  intro r r' he
  have hc : (compare).hom.app V r = (compare).hom.app V r' := by
    apply Subtype.ext
    apply (orbitBC (levelSubgroup V)).injective
    exact he
  have hinv : ∀ z : (rawD).obj V,
      (compare).inv.app V ((compare).hom.app V z) = z :=
    fun z => congrArg (fun k => k z) (NatTrans.congr_app (compare).hom_inv_id V)
  exact (hinv r).symm.trans
    ((congrArg ((compare).inv.app V) hc).trans (hinv r'))

end PointEquality

end ImageFixedPullback

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
