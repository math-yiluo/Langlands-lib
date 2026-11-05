import Langlands.Shimura.PEL.HarrisIntegralCMLevelImageFixedEquivalence
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitUniversalProperty

/-! # Direct levels on arbitrary connected tests of a finite Harris orbit cover -/

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

private def sectionFixedFiberEquiv
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (ht : ∀ Y : Cover X, Finite (Fiber t Y))
    (Y : Cover X) :
    (Over.mk (𝟙 X) ⟶ Y.obj) ≃
      {y : Fiber t Y // ∀ g : FundamentalGroup t ht, g • y = y} := by
  letI : (continuousActionFunctor t ht).IsEquivalence :=
    geometricContinuousActionEquivalence t ht
  let I : Cover X := cover (𝟙 X)
  let e : Fiber t I := Over.homMk t (by
    change t ≫ 𝟙 X = t
    simp)
  have uniq : ∀ x : Fiber t I, x = e := by
    intro x
    apply Over.OverMorphism.ext
    simpa [I, cover, e] using (Over.w x)
  let ev : (Over.mk (𝟙 X) ⟶ Y.obj) →
      {y : Fiber t Y // ∀ g : FundamentalGroup t ht, g • y = y} :=
    fun k => ⟨e ≫ k, fun g => by
      calc
        g • (e ≫ k) = (g • e) ≫ k :=
          smul_naturality t ht (ObjectProperty.homMk k : I ⟶ Y) g e
        _ = e ≫ k := congrArg (fun x : Fiber t I => x ≫ k) (uniq (g • e))⟩
  refine Equiv.ofBijective ev ⟨?_, ?_⟩
  · intro k l hkl
    have eqC : (ObjectProperty.homMk k : I ⟶ Y) =
        ObjectProperty.homMk l := by
      apply (continuousActionFunctor t ht).map_injective
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply FintypeCat.hom_ext
      intro x
      change x ≫ k = x ≫ l
      rw [uniq x]
      exact congrArg Subtype.val hkl
    exact congrArg (fun f : I ⟶ Y => f.hom) eqC
  · intro y
    let k : (continuousActionFunctor t ht).obj I ⟶
        (continuousActionFunctor t ht).obj Y :=
      ObjectProperty.homMk
        { hom := FintypeCat.homMk (fun _ => y.val)
          comm := by
            intro g
            apply FintypeCat.hom_ext
            intro _
            exact (y.property g).symm }
    let c : I ⟶ Y := (continuousActionFunctor t ht).preimage k
    refine ⟨c.hom, Subtype.ext ?_⟩
    exact congrArg (fun f : (continuousActionFunctor t ht).obj I ⟶
      (continuousActionFunctor t ht).obj Y => f.hom.hom e)
        ((continuousActionFunctor t ht).map_preimage k)

private theorem sectionFixedFiberEquiv_apply
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) (ht : ∀ Y : Cover X, Finite (Fiber t Y))
    (Y : Cover X) (k : Over.mk (𝟙 X) ⟶ Y.obj) :
    (sectionFixedFiberEquiv t ht Y k).val.left = t ≫ k.left := rfl

private def testSectionEquiv {X Z : Scheme.{0}} (f : X ⟶ Z) (Y : Cover Z) :
    (Over.mk f ⟶ Y.obj) ≃
      (Over.mk (𝟙 X) ⟶ ((pullbackFunctor f).obj Y).obj) where
  toFun k := Over.homMk
    (pullback.lift k.left (𝟙 X) (by simp))
    (pullback.lift_snd _ _ _)
  invFun k := Over.homMk (k.left ≫ pullback.fst Y.obj.hom f) (by
    have hk : k.left ≫ pullback.snd Y.obj.hom f = 𝟙 X := Over.w k
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk]
    simp)
  left_inv k := by
    apply Over.OverMorphism.ext
    simp
  right_inv k := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using (Over.w k).symm

private def testFixedFiberEquiv
    {X Z : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : X ⟶ Z) (t : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ Z)
    (es : t ≫ f = s)
    (ht : ∀ Y : Cover X, Finite (Fiber t Y))
    (hs : ∀ Y : Cover Z, Finite (Fiber s Y)) (Y : Cover Z) :
    (Over.mk f ⟶ Y.obj) ≃
      {y : Fiber s Y //
        ∀ g : FundamentalGroup t ht, fundamentalGroupMap f t s es ht hs g • y = y} := by
  let pb := pullbackFiberEquiv f t s es Y
  refine ((testSectionEquiv f Y).trans
    ((sectionFixedFiberEquiv t ht ((pullbackFunctor f).obj Y)).trans ?_))
  refine
    { toFun := fun y => ⟨pb.symm y.val, ?_⟩
      invFun := fun y => ⟨pb y.val, ?_⟩
      left_inv := fun _ => Subtype.ext (pb.apply_symm_apply _)
      right_inv := fun _ => Subtype.ext (pb.symm_apply_apply _) }
  · intro g
    apply pb.injective
    rw [pullbackFiberEquiv_smul f t s es ht hs g Y,
      pb.apply_symm_apply, y.property g]
  · intro g
    rw [← pullbackFiberEquiv_smul f t s es ht hs g Y, y.property g]

private theorem testFixedFiberEquiv_apply
    {X Z : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : X ⟶ Z) (t : Spec (.of Ω) ⟶ X) (s : Spec (.of Ω) ⟶ Z)
    (es : t ≫ f = s)
    (ht : ∀ Y : Cover X, Finite (Fiber t Y))
    (hs : ∀ Y : Cover Z, Finite (Fiber s Y)) (Y : Cover Z)
    (k : Over.mk f ⟶ Y.obj) :
    (testFixedFiberEquiv f t s es ht hs Y k).val.left = t ≫ k.left := by
  change ((pullbackFiberEquiv f t s es Y).symm
    (sectionFixedFiberEquiv t ht ((pullbackFunctor f).obj Y)
      (testSectionEquiv f Y k)).val).left = _
  rw [pullbackFiberEquiv_symm_apply_left, sectionFixedFiberEquiv_apply]
  change (t ≫ pullback.lift k.left (𝟙 X) _) ≫ pullback.fst Y.obj.hom f = _
  simp

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

/-- On an arbitrary connected locally noetherian test, maps into the actual
orbit cover are exactly orbit members fixed by the induced fundamental group. -/
def harrisIntegralCMFiniteOrbitCoverTestRawEquiv
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      (Over.mk f.left ⟶ (orbitCover U V hU q).obj) ≃
        {z : RawOrbits V // z ∈ MulAction.orbit Gamma q ∧
          ∀ g : FundamentalGroup t ht, alpha g • z = z} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  let e := fiberEquiv U V hU q
  refine (testFixedFiberEquiv f.left t s es ht hs (orbitCover U V hU q)).trans ?_
  refine
    { toFun := fun y => ⟨(e y.val).val, (e y.val).property, ?_⟩
      invFun := fun z => ⟨e.symm ⟨z.val, z.property.1⟩, ?_⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply y.val)
      right_inv := ?_ }
  · intro g
    calc
      alpha g • (e y.val).val = (e (alpha g • y.val)).val :=
        (congrArg Subtype.val (harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul
          D C P B W lam T a compatibility h s hs htor hu U V hU q (alpha g) y.val)).symm
      _ = (e y.val).val := congrArg (fun x => (e x).val) (y.property g)
  · intro g
    apply e.injective
    rw [harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul, e.apply_symm_apply]
    apply Subtype.ext
    exact z.property.2 g
  · intro z
    apply Subtype.ext
    have hz := congrArg Subtype.val (e.apply_symm_apply ⟨z.val, z.property.1⟩)
    exact hz

local notation "testRawEquiv" => harrisIntegralCMFiniteOrbitCoverTestRawEquiv
  D C P B W lam T a compatibility h s hs htor hu f t es ht

omit [IsCMField F] [IsScalarTower ℚ F A] [QuasiSeparatedSpace T'.left] in
/-- The correspondence evaluates the actual scheme morphism at the test point. -/
theorem harrisIntegralCMFiniteOrbitCoverTestRawEquiv_apply_val
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj),
      (testRawEquiv U V hU q k).val =
        (fiberEquiv U V hU q
          (Over.homMk (t ≫ k.left) (by rw [Category.assoc, Over.w k]; exact es))).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q k
  change (fiberEquiv U V hU q
    (testFixedFiberEquiv f.left t s es ht hs (orbitCover U V hU q) k).val).val = _
  apply congrArg (fun x => (fiberEquiv U V hU q x).val)
  apply Over.OverMorphism.ext
  exact testFixedFiberEquiv_apply f.left t s es ht hs (orbitCover U V hU q) k

variable
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "rawD" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T' ((relativeEndRestrict B f).comp a)
    compatibility h t ht htor huD
local notation "rawEvaluation" => harrisIntegralCMRestrictionRawClass
  D C P B W lam f a compatibility h t ht htor huD s es hs
local notation "directEquiv" => harrisIntegralCMRestrictionImageFixedEquivAt
  D C P B W lam f a compatibility h t ht htor hu huD s es hs

/-- The direct levels with target-orbit value correspond to the image-fixed
members of that orbit, via the original restriction evaluation. -/
def harrisIntegralCMTestLevelOrbitEvaluationEquiv
    (V : HarrisLevel D) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q} ≃
        {z : RawOrbits V // z ∈ MulAction.orbit Gamma q ∧
          ∀ g : FundamentalGroup t ht, alpha g • z = z} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  let e := directEquiv V
  have hev : ∀ l : (rawD).obj V, (e l).val = rawEvaluation V l :=
    harrisIntegralCMRestrictionImageFixedEquivAt_apply_val
      D C P B W lam f a compatibility h t ht htor hu huD s es hs V
  let ev : {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q} →
      {z : RawOrbits V // z ∈ MulAction.orbit Gamma q ∧
        ∀ g : FundamentalGroup t ht, alpha g • z = z} :=
    fun l => ⟨rawEvaluation V l.val, l.property, by
      rw [← hev]
      exact (e l.val).property⟩
  refine Equiv.ofBijective ev ⟨?_, ?_⟩
  · intro l l' he
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    rw [hev, hev]
    exact congrArg Subtype.val he
  · intro z
    let l := e.symm ⟨z.val, z.property.2⟩
    have hl : rawEvaluation V l = z.val :=
      (hev l).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨z.val, z.property.2⟩))
    exact ⟨⟨l, hl.symm ▸ z.property.1⟩, Subtype.ext hl⟩

local notation "testLevelEvaluationEquiv" => harrisIntegralCMTestLevelOrbitEvaluationEquiv
  D C P B W lam T a compatibility h s hs htor hu f t es ht huD

/-- Actual scheme maps from an arbitrary connected locally noetherian test
into the orbit cover correspond to direct levels with target-orbit value. -/
def harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V,
      (Over.mk f.left ⟶ (orbitCover U V hU q).obj) ≃
        {l : (rawD).obj V // rawEvaluation V l ∈ MulAction.orbit Gamma q} := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  exact (testRawEquiv U V hU q).trans (testLevelEvaluationEquiv V q).symm

local notation "testLevelEquiv" => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h s hs htor hu f t es ht huD

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Its original raw restriction value is evaluation of the scheme map at
`t`, followed by the actual geometric-fibre comparison. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val
    (U V : HarrisLevel D) (hU : Nonempty ((rawTower).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (k : Over.mk f.left ⟶ (orbitCover U V hU q).obj),
      rawEvaluation V (testLevelEquiv U V hU q k).val =
        (fiberEquiv U V hU q
          (Over.homMk (t ≫ k.left) (by rw [Category.assoc, Over.w k]; exact es))).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q k
  have he := congrArg Subtype.val
    ((testLevelEvaluationEquiv V q).apply_symm_apply (testRawEquiv U V hU q k))
  exact he.trans (harrisIntegralCMFiniteOrbitCoverTestRawEquiv_apply_val
    D C P B W lam T a compatibility h s hs htor hu f t es ht U V hU q k)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
