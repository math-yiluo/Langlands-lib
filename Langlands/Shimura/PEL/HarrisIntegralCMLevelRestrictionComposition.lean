import Langlands.Shimura.PEL.HarrisIntegralCMRestrictionFrames
import Langlands.AbelianScheme.Tate.WeilLevelBaseChangeCoherence

/-! # Composition of original Harris fixed-level restriction -/

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
    (f : T' ⟶ T)
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))


local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "aD" => (relativeEndRestrict B f).comp a
local notation "iT" => D.harrisHodgePELRationalAction C BT a

variable (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω]

local notation "H" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "HP" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "FrameAt" T₀:max a₀:max s₀:max => harrisIntegralCMWeilFrame
  D C P B W lam T₀ a₀ compatibility h s₀
local notation "rightAt" T₀:max a₀:max s₀:max =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability
    (W.pullback P (T₀).hom).hasDual (W.pullback P (T₀).hom).geometry
    (W.pullback P (T₀).hom).inverseBundle (W.pullback P (T₀).hom).evaluation
    compatibility (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀
local notation "RawAt" T₀:max a₀:max s₀:max U₀:max =>
  @RightOrbit H _ (FrameAt T₀ a₀ s₀) (rightAt T₀ a₀ s₀) U₀
variable (htor : TorsionFiniteEtaleStatement.{0})

local notation "monAt" T₀:max a₀:max s₀:max hs₀:max hu₀:max =>
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (W.pullback P (T₀).hom).hasDual
    (W.pullback P (T₀).hom).geometry (W.pullback P (T₀).hom).inverseBundle
    (W.pullback P (T₀).hom).evaluation
    (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀ hs₀ htor hu₀
local notation "commAt" T₀:max a₀:max s₀:max hs₀:max hu₀:max =>
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (W.pullback P (T₀).hom).hasDual
    (W.pullback P (T₀).hom).geometry (W.pullback P (T₀).hom).inverseBundle
    (W.pullback P (T₀).hom).evaluation
    (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀ hs₀ htor hu₀
local notation "towerAt" T₀:max a₀:max s₀:max hs₀:max hu₀:max =>
  harrisIntegralCMFullActionLevelTower D C P B W lam T₀ a₀ compatibility h s₀ hs₀ htor hu₀
local notation "levelSubgroup" V => ((hodgeLevelFunctor D C).obj V).subgroup

section ActionEquality

variable
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual action-equality frame comparison intertwines monodromy. -/
theorem harrisIntegralCMWeilFrameActionEq_monodromy
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) (hs : ∀ Y : Cover T.left, Finite (Fiber s Y)) :
    letI := monAt T a s hs huT
    letI := monAt T a' s hs huT
    ∀ (z : FundamentalGroup s hs) (eta : FrameAt T a s),
      harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h a' ha s
          (z • eta) =
        z • harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h
          a' ha s eta := by
  let := monAt T a s hs huT
  let := monAt T a' s hs huT
  intro z eta
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

/-- Literal action equality compares the original monodromy-fixed levels. -/
def harrisIntegralCMFullActionLevelActionEquiv
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (V : HarrisLevel D) :
    (towerAt T a s hs huT).obj V ≃ (towerAt T a' s hs huT).obj V := by
  let := rightAt T a s
  let := rightAt T a' s
  let : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  let : MulAction HPᵐᵒᵖ (FrameAt T a' s) := rightAt T a' s
  let := monAt T a s hs huT
  let := monAt T a' s hs huT
  let := commAt T a s hs huT
  let := commAt T a' s hs huT
  let : SMulCommClass (FundamentalGroup s hs) HPᵐᵒᵖ (FrameAt T a s) :=
    commAt T a s hs huT
  let : SMulCommClass (FundamentalGroup s hs) HPᵐᵒᵖ (FrameAt T a' s) :=
    commAt T a' s hs huT
  exact InvariantOrbit.equiv (levelSubgroup V) (MulEquiv.refl (FundamentalGroup s hs))
    (harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h a' ha s)
    (harrisIntegralCMWeilFrameActionEq_right D C P B W lam a compatibility h a' ha s)
    (harrisIntegralCMWeilFrameActionEq_monodromy
      D C P B W lam a compatibility h htor huT a' ha s hs)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The fixed-level comparison has exactly the constructed raw action-equality value. -/
theorem harrisIntegralCMFullActionLevelActionEquiv_val
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (V : HarrisLevel D) (r : (towerAt T a s hs huT).obj V) :
    (harrisIntegralCMFullActionLevelActionEquiv
        D C P B W lam a compatibility h htor huT a' ha s hs V r).val =
      harrisIntegralCMWeilRawActionEq D C P B W lam a compatibility h a' ha s
        (levelSubgroup V) r.val := rfl

/-- The fixed-level action comparison retains every original Harris level arrow. -/
def harrisIntegralCMFullActionLevelActionIso
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) (hs : ∀ Y : Cover T.left, Finite (Fiber s Y)) :
    towerAt T a s hs huT ≅ towerAt T a' s hs huT :=
  NatIso.ofComponents (fun V =>
    (harrisIntegralCMFullActionLevelActionEquiv
      D C P B W lam a compatibility h htor huT a' ha s hs V).toIso) (by
    intro V Z j
    let := rightAt T a s
    let := rightAt T a' s
    ext r
    apply Subtype.ext
    exact RightOrbit.map_translate
      (harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h a' ha s)
      (harrisIntegralCMWeilFrameActionEq_right D C P B W lam a compatibility h a' ha s)
      ((hodgeLevelFunctor D C).map j).element
      ((hodgeLevelFunctor D C).map j).respects r.val)

end ActionEquality

section Composition

variable {T'' : Over S} [QuasiSeparatedSpace T''.left] (g : T'' ⟶ T')
    (u : Spec (.of Ω) ⟶ T''.left)
    (hU : ∀ Y : Cover T''.left, Finite (Fiber u Y))
    (hG : ∀ Y : Cover T'.left, Finite (Fiber (u ≫ g.left) Y))
    (hC : ∀ Y : Cover T.left, Finite (Fiber (u ≫ (g ≫ f).left) Y))
    (hF : ∀ Y : Cover T.left, Finite (Fiber ((u ≫ g.left) ≫ f.left) Y))
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    (huU : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T''.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]
    [hμfinU : ∀ k : Index (fun _ => True), IsFinite (mu T''.left k.val).X.hom]
    [hμetU : ∀ k : Index (fun _ => True), Etale (mu T''.left k.val).X.hom]

local notation "aComposite" => (relativeEndRestrict B (g ≫ f)).comp a
local notation "aSuccessive" => (relativeEndRestrict B g).comp aD
local notation "resF" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam f a compatibility h (u ≫ g.left) hG hF htor huT huD
local notation "resG" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam g aD compatibility h u hU hG htor huD huU
local notation "resC" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam (g ≫ f) a compatibility h u hU hC htor huT huU
local notation "evalF" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam f a compatibility h (u ≫ g.left)
local notation "evalG" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam g aD compatibility h u
local notation "evalC" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam (g ≫ f) a compatibility h u
local notation "pointComp" V:max => Tate.weilAdelicLevelPointEq
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability (WT).hasDual (WT).geometry (WT).inverseBundle
  (WT).evaluation compatibility lamT h iT A (D.harrisHodgePELForm C)
  (Category.assoc u g.left f.left).symm hC hF htor huT (levelSubgroup V)

/-- The original fixed-level towers of composite and successive restricted
integral actions are canonically isomorphic. -/
def harrisIntegralCMFullActionLevelRestrictionCompIso :
    towerAt T'' aComposite u hU huU ≅ towerAt T'' aSuccessive u hU huU :=
  harrisIntegralCMFullActionLevelActionIso
    D C P B W lam aComposite compatibility h htor huU aSuccessive
    (harrisIntegralCMRestrictionAction_comp D C B f g a).symm u hU

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original fixed-level restriction composes under the constructed comparison
of literal restricted actions and the canonical associativity of the point. -/
theorem harrisIntegralCMFullActionLevelRestriction_comp
    (V : HarrisLevel D) (r : (towerAt T a (u ≫ (g ≫ f).left) hC huT).obj V) :
    (harrisIntegralCMFullActionLevelRestrictionCompIso
        D C P B W lam f a compatibility h htor g u hU huU).hom.app V
        ((resC).app V r) =
      (resG).app V ((resF).app V ((pointComp V) r)) := by
  apply Subtype.ext
  change (harrisIntegralCMFullActionLevelActionEquiv
    D C P B W lam aComposite compatibility h htor huU aSuccessive
    (harrisIntegralCMRestrictionAction_comp D C B f g a).symm u hU V
    ((resC).app V r)).val = _
  rw [harrisIntegralCMFullActionLevelActionEquiv_val]
  change harrisIntegralCMRestrictionRawCompEquiv D C P B W lam f a compatibility h
    g u (levelSubgroup V) ((resC).app V r).val = _
  apply (evalG (levelSubgroup V)).injective
  apply (evalF (levelSubgroup V)).injective
  rw [harrisIntegralCMRestrictionRaw_comp]
  rw [harrisIntegralCMFullActionLevelRestriction_rawValue
    D C P B W lam (g ≫ f) a compatibility h u hU hC htor huU huT V r]
  rw [harrisIntegralCMFullActionLevelRestriction_rawValue
    D C P B W lam g aD compatibility h u hU hG htor huU huD V
    ((resF).app V ((pointComp V) r))]
  rw [harrisIntegralCMFullActionLevelRestriction_rawValue
    D C P B W lam f a compatibility h (u ≫ g.left) hG hF htor huD huT V
    ((pointComp V) r)]
  exact (Tate.weilAdelicLevelPointEq_val P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) (Category.assoc u g.left f.left).symm hC hF htor huT
    (levelSubgroup V) r).symm

end Composition

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
