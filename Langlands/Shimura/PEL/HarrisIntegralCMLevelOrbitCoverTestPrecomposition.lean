import Langlands.Shimura.PEL.HarrisIntegralCMLevelRestrictionComposition
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverTestEquivalence

/-! # Test precomposition of original Harris orbit-cover levels -/

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

section PointEvaluation

variable (t : Spec (.of Ω) ⟶ T'.left)
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original raw evaluation at a propositionally specified point is the actual
raw frame evaluation followed by the canonical point-equality map. -/
theorem harrisIntegralCMRestrictionRawClass_eq_pointEquiv
    (s : Spec (.of Ω) ⟶ T.left) (es : t ≫ f.left = s)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (V : HarrisLevel D) (r : (towerAt T' aD t ht huD).obj V) :
    harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        t ht htor huD s es hs V r =
      Tate.weilAdelicFrameRightOrbitPointEq P.preservation P.composition
        P.unitCoherence P.associativity P.comparison P.symmetry P.stability
        (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
        compatibility lamT h iT A (D.harrisHodgePELForm C) es (levelSubgroup V)
        (harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h
          t (levelSubgroup V) r.val) := by
  subst s
  rw [harrisIntegralCMRestrictionRawClass_eq_rawEquiv]
  generalize harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h
    t (levelSubgroup V) r.val = q
  induction q using Quotient.inductionOn with
  | h eta => rfl

end PointEvaluation

section Precomposition

variable {T'' : Over S} [QuasiSeparatedSpace T''.left] (g : T'' ⟶ T')
    (u : Spec (.of Ω) ⟶ T''.left)
    (hU : ∀ Y : Cover T''.left, Finite (Fiber u Y))
    (hG : ∀ Y : Cover T'.left, Finite (Fiber (u ≫ g.left) Y))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    (huU : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T''.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]
    [hμfinU : ∀ k : Index (fun _ => True), IsFinite (mu T''.left k.val).X.hom]
    [hμetU : ∀ k : Index (fun _ => True), Etale (mu T''.left k.val).X.hom]

local notation "aComposite" => (relativeEndRestrict B (g ≫ f)).comp a
local notation "resG" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam g aD compatibility h u hU hG htor huD huU
local notation "compIso" => harrisIntegralCMFullActionLevelRestrictionCompIso
  D C P B W lam f a compatibility h htor g u hU huU
local notation "evalF" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam f a compatibility h (u ≫ g.left)
local notation "evalG" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam g aD compatibility h u
local notation "evalC" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam (g ≫ f) a compatibility h u

/-- Restrict the original direct level along the new test morphism, then
use the constructed inverse comparison with the composite literal action. -/
def harrisIntegralCMFullActionLevelPrecomposition :
    towerAt T' aD (u ≫ g.left) hG huD ⟶ towerAt T'' aComposite u hU huU :=
  resG ≫ (compIso).inv

local notation "precomp" => harrisIntegralCMFullActionLevelPrecomposition
  D C P B W lam f a compatibility h htor g u hU hG huD huU

omit [IsCMField F] [IsScalarTower ℚ F A] [QuasiSeparatedSpace T.left] in
/-- The precomposition map uses exactly original restriction and the inverse
of the constructed comparison, in every level. -/
theorem harrisIntegralCMFullActionLevelPrecomposition_apply
    (V : HarrisLevel D) (r : (towerAt T' aD (u ≫ g.left) hG huD).obj V) :
    (precomp).app V r = (compIso).inv.app V ((resG).app V r) := rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original raw evaluation is unchanged by test precomposition, retaining
an arbitrary propositional base-point equation. -/
theorem harrisIntegralCMRestrictionRawClass_precomposition
    (s : Spec (.of Ω) ⟶ T.left) (es : (u ≫ g.left) ≫ f.left = s)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (V : HarrisLevel D) (r : (towerAt T' aD (u ≫ g.left) hG huD).obj V) :
    harrisIntegralCMRestrictionRawClass D C P B W lam (g ≫ f) a compatibility h
        u hU htor huU s ((Category.assoc u g.left f.left).symm.trans es) hs V
        ((precomp).app V r) =
      harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        (u ≫ g.left) hG htor huD s es hs V r := by
  subst s
  rw [harrisIntegralCMRestrictionRawClass_eq_rawEquiv]
  rw [harrisIntegralCMRestrictionRawClass_eq_pointEquiv]
  have hc : harrisIntegralCMRestrictionRawCompEquiv
      D C P B W lam f a compatibility h g u (levelSubgroup V)
      ((precomp).app V r).val = ((resG).app V r).val := by
    change ((compIso).hom.app V ((compIso).inv.app V ((resG).app V r))).val = _
    have he := congrArg (fun k => k ((resG).app V r))
      (NatTrans.congr_app (compIso).inv_hom_id V)
    exact congrArg Subtype.val he
  refine (harrisIntegralCMRestrictionRaw_comp D C P B W lam f a compatibility h
    g u (levelSubgroup V) ((precomp).app V r).val).symm.trans ?_
  rw [hc]
  rw [harrisIntegralCMFullActionLevelRestriction_rawValue
    D C P B W lam g aD compatibility h u hU hG htor huU huD V r]

section OrbitPrecomposition

variable (s : Spec (.of Ω) ⟶ T.left) (es : (u ≫ g.left) ≫ f.left = s)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "Gamma" => FundamentalGroup s hs
local notation "rawD" => towerAt T' aD (u ≫ g.left) hG huD
local notation "rawC" => towerAt T'' aComposite u hU huU
local notation "rawEvaluation" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h (u ≫ g.left) hG htor huD s es hs
local notation "rawCompositeEvaluation" => harrisIntegralCMRestrictionRawClass
  D C P B W lam (g ≫ f) a compatibility h u hU htor huU s
    ((Category.assoc u g.left f.left).symm.trans es) hs

/-- The original restriction map, followed by inverse composite-action
comparison, preserves the selected base monodromy orbit. -/
def harrisIntegralCMTestLevelOrbitPrecomposition (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ q : RightOrbit (FrameAt T a s) (levelSubgroup V),
      {r : (rawD).obj V // rawEvaluation V r ∈ MulAction.orbit Gamma q} →
      {r : (rawC).obj V // rawCompositeEvaluation V r ∈ MulAction.orbit Gamma q} := by
  letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  intro q r
  refine ⟨(precomp).app V r.val, ?_⟩
  rw [harrisIntegralCMRestrictionRawClass_precomposition
    D C P B W lam f a compatibility h htor g u hU hG huD huU s es hs V r.val]
  exact r.property

local notation "orbitPrecomp" => harrisIntegralCMTestLevelOrbitPrecomposition
  D C P B W lam f a compatibility h htor g u hU hG huD huU s es hs huT

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The orbit-subtype precomposition has the original fixed-level map as its value. -/
theorem harrisIntegralCMTestLevelOrbitPrecomposition_val (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (r : {r : (rawD).obj V // rawEvaluation V r ∈ MulAction.orbit Gamma q}),
      (orbitPrecomp V q r).val = (compIso).inv.app V ((resG).app V r.val) := by
  intro q r
  rfl

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]
    [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left]
    [ConnectedSpace T''.left] [IsLocallyNoetherian T''.left]

local notation "rawTower" => towerAt T a s hs huT
local notation "orbitCover" => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h s hs htor huT
local notation "fiberEquiv" => harrisIntegralCMFiniteOrbitCoverFiberEquiv
  D C P B W lam T a compatibility h s hs htor huT
local notation "testEquivF" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor huT f (u ≫ g.left) es hG huD
local notation "testEquivC" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor huT (g ≫ f) u
    ((Category.assoc u g.left f.left).symm.trans es) hU huU

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On arbitrary connected locally noetherian tests, the selected direct-level
precomposition is actual scheme-morphism precomposition into the orbit cover. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_precomposition
    (U V : HarrisLevel D) (hRef : Nonempty ((rawTower).obj U)) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (k : Over.mk f.left ⟶ (orbitCover U V hRef q).obj),
      orbitPrecomp V q (testEquivF U V hRef q k) =
        testEquivC U V hRef q
          ((Over.homMk g.left rfl : Over.mk (g ≫ f).left ⟶ Over.mk f.left) ≫ k) := by
  let : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  let : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  let : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  intro q k
  apply Subtype.ext
  apply harrisIntegralCMRestrictionRawClass_injective
    D C P B W lam (g ≫ f) a compatibility h u hU htor huU s
      ((Category.assoc u g.left f.left).symm.trans es) hs V
  change rawCompositeEvaluation V ((precomp).app V (testEquivF U V hRef q k).val) = _
  rw [harrisIntegralCMRestrictionRawClass_precomposition
    D C P B W lam f a compatibility h htor g u hU hG huD huU s es hs V]
  rw [harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val,
    harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val]
  apply congrArg (fun x => (fiberEquiv U V hRef q x).val)
  apply Over.OverMorphism.ext
  exact Category.assoc u g.left k.left

end OrbitPrecomposition

end Precomposition

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
