import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverEvaluation

/-! # Exact image of the actual orbit-cover Hom-to-level comparison -/

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


local notation "homRawMap" => harrisIntegralCMFiniteOrbitCoverHomRawMap
  D C P B W lam T a compatibility h s hs htor hu
local notation "homLevel" => harrisIntegralCMFiniteOrbitCoverHomLevel
  D C P B W lam T a compatibility h s hs htor hu

/-- Evaluate actual cover morphisms on a pretransitive source fibre. Their
values are exactly the target-orbit classes fixed by the full point stabilizer. -/
def harrisIntegralCMFiniteOrbitCoverHomEvaluationEquiv
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left) (x : Fiber s Y)
      [MulAction.IsPretransitive Gamma (Fiber s Y)],
      (Y ⟶ orbitCover U V hU q) ≃
        {z : RawOrbits V // z ∈ MulAction.orbit Gamma q ∧
          ∀ g : Gamma, g • x = x → g • z = z} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y x instTrans
  let ev : (Y ⟶ orbitCover U V hU q) →
      {z : RawOrbits V // z ∈ MulAction.orbit Gamma q ∧
        ∀ g : Gamma, g • x = x → g • z = z} := fun f =>
    ⟨homRawMap U V hU q Y f x,
      (fiberEquiv U V hU q (x ≫ f.hom)).property,
      fun g hg => ((homRawMap U V hU q Y f).map_smul g x).symm.trans
        (congrArg (homRawMap U V hU q Y f) hg)⟩
  refine Equiv.ofBijective ev ⟨?_, ?_⟩
  · intro f k he
    apply harrisIntegralCMFiniteOrbitCoverHomRawMap_injective
      D C P B W lam T a compatibility h s hs htor hu U V hU q Y
    apply Langlands.GroupTheory.equivariantMap_evaluation_injective x
    have hv := congrArg Subtype.val he
    exact hv
  · intro z
    let z' : {v : MulAction.orbit Gamma q //
        ∀ g : Gamma, g • x = x → g • v = v} :=
      ⟨⟨z.val, z.property.1⟩, fun g hg => Subtype.ext (z.property.2 g hg)⟩
    let k : Fiber s Y →[Gamma] MulAction.orbit Gamma q :=
      (Langlands.GroupTheory.transitiveActionEvaluationEquiv x).symm z'
    obtain ⟨f, hf, _⟩ := harrisIntegralCMFiniteOrbitCover_existsUnique
      D C P B W lam T a compatibility h s hs htor hu U V hU q Y k
      (fun g y => k.map_smul g y)
    refine ⟨f, Subtype.ext ?_⟩
    have hk : k x = z'.val := congrArg Subtype.val
      ((Langlands.GroupTheory.transitiveActionEvaluationEquiv x).apply_symm_apply z')
    exact (congrArg Subtype.val (hf x)).trans (congrArg Subtype.val hk)

local notation "homEvaluationEquiv" => harrisIntegralCMFiniteOrbitCoverHomEvaluationEquiv
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The evaluation equivalence is literal raw-valued evaluation at the chosen lift. -/
theorem harrisIntegralCMFiniteOrbitCoverHomEvaluationEquiv_apply_val
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left) (x : Fiber s Y)
      [MulAction.IsPretransitive Gamma (Fiber s Y)]
      (f : Y ⟶ orbitCover U V hU q),
      (homEvaluationEquiv U V hU q Y x f).val =
        (fiberEquiv U V hU q (x ≫ f.hom)).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y x instTrans f
  rfl

/-- Actual morphisms between selected covers correspond exactly to direct
levels whose evaluated class lies in the target orbit and is fixed by the full
stabilizer of the distinguished source lift. -/
def harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom],
        (Y ⟶ orbitCover U Z hU r) ≃
          {l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
              ((relativeEndRestrict B fq).comp a)
              compatibility h x.left ht htor huY).obj Z //
            let z := harrisIntegralCMRestrictionRawClass D C P B W lam fq a
              compatibility h x.left ht htor huY s (Over.w x) hs Z l
            z ∈ MulAction.orbit Gamma r ∧
              ∀ g : Gamma, g • x = x → g • z = z} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt
  let Y := orbitCover U V hU q
  let x := coverPoint U V hU q
  let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
  let fq : Tq ⟶ T := Over.homMk Y.obj.hom rfl
  letI : IsFinite fq.left := Y.property.1
  letI : Etale fq.left := Y.property.2
  letI : QuasiSeparatedSpace Tq.left := instQS
  letI : ∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom := instMuFin
  letI : ∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom := instMuEt
  letI : MulAction.IsPretransitive Gamma (Fiber s Y) :=
    harrisIntegralCMFiniteOrbitCoverFiber_pretransitive
      D C P B W lam T a compatibility h s hs htor hu U V hU q
  let ev := homEvaluationEquiv U Z hU r Y x
  let rawEvaluation := harrisIntegralCMRestrictionRawClass D C P B W lam fq a
    compatibility h x.left ht htor huY s (Over.w x) hs Z
  let encode : (Y ⟶ orbitCover U Z hU r) →
      {l : (harrisIntegralCMFullActionLevelTower D C P B W lam Tq
          ((relativeEndRestrict B fq).comp a)
          compatibility h x.left ht htor huY).obj Z //
        rawEvaluation l ∈ MulAction.orbit Gamma r ∧
          ∀ g : Gamma, g • x = x → g • rawEvaluation l = rawEvaluation l} :=
    fun f => ⟨homLevel U V Z hU q r ht huY f, by
      dsimp only [rawEvaluation]
      rw [harrisIntegralCMFiniteOrbitCoverHomLevel_val]
      exact (ev f).property⟩
  refine Equiv.ofBijective encode ⟨?_, ?_⟩
  · intro f k he
    apply harrisIntegralCMFiniteOrbitCoverHomLevel_injective
      D C P B W lam T a compatibility h s hs htor hu U V Z hU q r ht huY
    have hv := congrArg Subtype.val he
    exact hv
  · intro l
    let v : {z : RawOrbits Z // z ∈ MulAction.orbit Gamma r ∧
        ∀ g : Gamma, g • x = x → g • z = z} :=
      ⟨rawEvaluation l.val, l.property⟩
    let f := ev.symm v
    refine ⟨f, Subtype.ext ?_⟩
    apply harrisIntegralCMRestrictionRawClass_injective
      D C P B W lam fq a compatibility h x.left ht htor huY s (Over.w x) hs Z
    change rawEvaluation (homLevel U V Z hU q r ht huY f) = rawEvaluation l.val
    dsimp only [rawEvaluation]
    rw [harrisIntegralCMFiniteOrbitCoverHomLevel_val]
    have hf := congrArg Subtype.val (ev.apply_symm_apply v)
    exact hf

local notation "homLevelRangeEquiv" => harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The range equivalence uses the original direct Hom-to-level construction. -/
theorem harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv_apply_val
    (U V Z : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z),
      let Y := orbitCover U V hU q
      let x := coverPoint U V hU q
      let Tq : Over S := Over.mk (Y.obj.hom ≫ T.hom)
      ∀ [QuasiSeparatedSpace Tq.left]
        (ht : ∀ J : Cover Y.obj.left, Finite (Fiber x.left J))
        (huY : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Y.obj.left, ⊤)))
        [∀ k : Index (fun _ => True), IsFinite (mu Tq.left k.val).X.hom]
        [∀ k : Index (fun _ => True), Etale (mu Tq.left k.val).X.hom]
        (f : Y ⟶ orbitCover U Z hU r),
        (homLevelRangeEquiv U V Z hU q r ht huY f).val =
          homLevel U V Z hU q r ht huY f := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  dsimp only
  intro q r instQS ht huY instMuFin instMuEt f
  rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
