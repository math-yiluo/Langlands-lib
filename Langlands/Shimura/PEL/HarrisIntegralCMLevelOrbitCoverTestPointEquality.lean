import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverTestPrecomposition

/-! # Equality of test points in original Harris orbit-cover levels -/

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

section PointEquality

variable (t t' : Spec (.of Ω) ⟶ T'.left) (et : t = t')
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (ht' : ∀ Y : Cover T'.left, Finite (Fiber t' Y))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]
    (s : Spec (.of Ω) ⟶ T.left) (es : t ≫ f.left = s) (es' : t' ≫ f.left = s)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))

local notation "pointLevelEquiv" V:max => Tate.weilAdelicLevelPointEq
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability (W.pullback P T'.hom).hasDual
  (W.pullback P T'.hom).geometry (W.pullback P T'.hom).inverseBundle
  (W.pullback P T'.hom).evaluation compatibility
  (W.pullbackMap P T'.hom (W.pullback P T'.hom) lam) h
  (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange T'.hom).obj B) aD)
  A (D.harrisHodgePELForm C) et ht ht' htor huD (levelSubgroup V)
local notation "rawD" => towerAt T' aD t ht huD
local notation "rawD'" => towerAt T' aD t' ht' huD
local notation "evalD" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h t ht htor huD s es hs
local notation "evalD'" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h t' ht' htor huD s es' hs

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Canonical equality transport of the test point preserves original raw evaluation. -/
theorem harrisIntegralCMRestrictionRawClass_pointEq
    (V : HarrisLevel D) (r : (rawD).obj V) :
    evalD' V ((pointLevelEquiv V) r) = evalD V r := by
  subst t'
  rfl

variable (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "Gamma" => FundamentalGroup s hs

/-- Restrict canonical fixed-level point-equality transport to a selected base orbit. -/
def harrisIntegralCMTestLevelOrbitPointEq (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ q : RightOrbit (FrameAt T a s) (levelSubgroup V),
      {r : (rawD).obj V // evalD V r ∈ MulAction.orbit Gamma q} ≃
        {r : (rawD').obj V // evalD' V r ∈ MulAction.orbit Gamma q} := by
  letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  intro q
  exact (pointLevelEquiv V).subtypeEquiv (fun r => by
    rw [harrisIntegralCMRestrictionRawClass_pointEq
      D C P B W lam f a compatibility h htor t t' et ht ht' huD s es es' hs V r])

local notation "orbitPointEq" => harrisIntegralCMTestLevelOrbitPointEq
  D C P B W lam f a compatibility h htor t t' et ht ht' huD s es es' hs huT

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The selected-orbit equivalence uses the existing fixed-level equality map. -/
theorem harrisIntegralCMTestLevelOrbitPointEq_val (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (r : {r : (rawD).obj V // evalD V r ∈ MulAction.orbit Gamma q}),
      (orbitPointEq V q r).val = (pointLevelEquiv V) r.val := by
  intro q r
  rfl

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]
    [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left]

local notation "rawTower" => towerAt T a s hs huT
local notation "orbitCover" => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h s hs htor huT
local notation "fiberEquiv" => harrisIntegralCMFiniteOrbitCoverFiberEquiv
  D C P B W lam T a compatibility h s hs htor huT
local notation "testEquiv" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor huT f t es ht huD
local notation "testEquiv'" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor huT f t' es' ht' huD

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual test-cover correspondence respects canonical equality of test points. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointEq
    (U V : HarrisLevel D) (hRef : Nonempty ((rawTower).obj U)) :
    let : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    let : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    let : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (k : Over.mk f.left ⟶ (orbitCover U V hRef q).obj),
      orbitPointEq V q (testEquiv U V hRef q k) = testEquiv' U V hRef q k := by
  let : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  let : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  let : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  dsimp only
  intro q k
  apply Subtype.ext
  apply harrisIntegralCMRestrictionRawClass_injective
    D C P B W lam f a compatibility h t' ht' htor huD s es' hs V
  change evalD' V ((pointLevelEquiv V) (testEquiv U V hRef q k).val) = _
  rw [harrisIntegralCMRestrictionRawClass_pointEq
    D C P B W lam f a compatibility h htor t t' et ht ht' huD s es es' hs V]
  rw [harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val,
    harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val]
  apply congrArg (fun x => (fiberEquiv U V hRef q x).val)
  apply Over.OverMorphism.ext
  exact congrArg (fun v => v ≫ k.left) et

end PointEquality

section PrecompositionAt

variable {T'' : Over S} [QuasiSeparatedSpace T''.left] (g : T'' ⟶ T')
    (u : Spec (.of Ω) ⟶ T''.left) (t : Spec (.of Ω) ⟶ T'.left)
    (et : u ≫ g.left = t)
    (hU : ∀ Y : Cover T''.left, Finite (Fiber u Y))
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (hG : ∀ Y : Cover T'.left, Finite (Fiber (u ≫ g.left) Y))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    (huU : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T''.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]
    [hμfinU : ∀ k : Index (fun _ => True), IsFinite (mu T''.left k.val).X.hom]
    [hμetU : ∀ k : Index (fun _ => True), Etale (mu T''.left k.val).X.hom]
    (s : Spec (.of Ω) ⟶ T.left) (es : t ≫ f.left = s)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "esG" => (congrArg (fun v => v ≫ f.left) et).trans es
local notation "esC" => (Category.assoc u g.left f.left).symm.trans esG
local notation "aComposite" => (relativeEndRestrict B (g ≫ f)).comp a
local notation "Gamma" => FundamentalGroup s hs
local notation "rawD" => towerAt T' aD t ht huD
local notation "rawC" => towerAt T'' aComposite u hU huU
local notation "evalD" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h t ht htor huD s es hs
local notation "evalC" => harrisIntegralCMRestrictionRawClass
  D C P B W lam (g ≫ f) a compatibility h u hU htor huU s esC hs
local notation "pointToInduced" => harrisIntegralCMTestLevelOrbitPointEq
  D C P B W lam f a compatibility h htor t (u ≫ g.left) et.symm ht hG huD
    s es esG hs huT
local notation "precompInduced" => harrisIntegralCMTestLevelOrbitPrecomposition
  D C P B W lam f a compatibility h htor g u hU hG huD huU s esG hs huT
local notation "fullPrecomp" => harrisIntegralCMFullActionLevelPrecomposition
  D C P B W lam f a compatibility h htor g u hU hG huD huU

/-- Canonically identify the supplied test point with the induced point, then
apply original restriction and the inverse composite-action comparison. -/
def harrisIntegralCMTestLevelOrbitPrecompositionAt (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ q : RightOrbit (FrameAt T a s) (levelSubgroup V),
      {r : (rawD).obj V // evalD V r ∈ MulAction.orbit Gamma q} →
        {r : (rawC).obj V // evalC V r ∈ MulAction.orbit Gamma q} := by
  letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  intro q r
  exact precompInduced V q (pointToInduced V q r)

local notation "precompAt" => harrisIntegralCMTestLevelOrbitPrecompositionAt
  D C P B W lam f a compatibility h htor g u t et hU ht hG huD huU s es hs huT

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The underlying value is original precomposition after canonical fixed-level point transport. -/
theorem harrisIntegralCMTestLevelOrbitPrecompositionAt_val (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (r : {r : (rawD).obj V // evalD V r ∈ MulAction.orbit Gamma q}),
      (precompAt V q r).val = (fullPrecomp).app V (pointToInduced V q r).val := by
  intro q r
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Supplied-point precomposition preserves the original raw evaluation. -/
theorem harrisIntegralCMRestrictionRawClass_precompositionAt (V : HarrisLevel D) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (r : {r : (rawD).obj V // evalD V r ∈ MulAction.orbit Gamma q}),
      evalC V (precompAt V q r).val = evalD V r.val := by
  let : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  let : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  let : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  intro q r
  change evalC V ((fullPrecomp).app V (pointToInduced V q r).val) = _
  rw [harrisIntegralCMRestrictionRawClass_precomposition
    D C P B W lam f a compatibility h htor g u hU hG huD huU s esG hs V]
  exact harrisIntegralCMRestrictionRawClass_pointEq
    D C P B W lam f a compatibility h htor t (u ≫ g.left) et.symm ht hG huD
      s es esG hs V r.val

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left] [IsAlgClosed Ω]
    [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left]
    [ConnectedSpace T''.left] [IsLocallyNoetherian T''.left]

local notation "rawTower" => towerAt T a s hs huT
local notation "orbitCover" => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h s hs htor huT
local notation "testEquivT" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor huT f t es ht huD
local notation "testEquivC" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor huT (g ≫ f) u esC hU huU

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual test precomposition commutes with the orbit-cover equivalences
for independently supplied test points and their compatibility equality. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_precompositionAt
    (U V : HarrisLevel D) (hRef : Nonempty ((rawTower).obj U)) :
    letI : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
    letI : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
    letI : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
    ∀ (q : RightOrbit (FrameAt T a s) (levelSubgroup V))
      (k : Over.mk f.left ⟶ (orbitCover U V hRef q).obj),
      precompAt V q (testEquivT U V hRef q k) =
        testEquivC U V hRef q
          ((Over.homMk g.left rfl : Over.mk (g ≫ f).left ⟶ Over.mk f.left) ≫ k) := by
  let : MulAction HPᵐᵒᵖ (FrameAt T a s) := rightAt T a s
  let : MulAction Gamma (FrameAt T a s) := monAt T a s hs huT
  let : SMulCommClass Gamma HPᵐᵒᵖ (FrameAt T a s) := commAt T a s hs huT
  intro q k
  change precompInduced V q (pointToInduced V q (testEquivT U V hRef q k)) = _
  rw [harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointEq
    D C P B W lam f a compatibility h htor t (u ≫ g.left) et.symm ht hG huD
      s es esG hs huT U V hRef q k]
  exact harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_precomposition
    D C P B W lam f a compatibility h htor g u hU hG huD huU s esG hs huT
      U V hRef q k

end PrecompositionAt

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
