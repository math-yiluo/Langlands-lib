import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverMaps
import Mathlib.CategoryTheory.Yoneda

/-! # The Hom universal property of finite-etale Harris orbit covers -/

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

/-- Actual maps into the chosen cover correspond to equivariant maps into the raw orbit. -/
def harrisIntegralCMFiniteOrbitCoverHomEquiv
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left),
      (Y ⟶ orbitCover U V hU q) ≃
        ((continuousActionFunctor s hs).obj Y ⟶ orbitAction U V hU q) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  letI : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro q Y
  refine
    { toFun := fun f => (continuousActionFunctor s hs).map f ≫ (orbitIso U V hU q).hom
      invFun := fun k => (continuousActionFunctor s hs).preimage
        (k ≫ (orbitIso U V hU q).inv)
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply (continuousActionFunctor s hs).map_injective
    simp
  · intro k
    simp

local notation "homEquiv" => harrisIntegralCMFiniteOrbitCoverHomEquiv
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The Hom correspondence evaluates by the actual geometric-fibre comparison. -/
theorem harrisIntegralCMFiniteOrbitCoverHomEquiv_apply
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left) (f : Y ⟶ orbitCover U V hU q)
      (x : Fiber s Y),
      (homEquiv U V hU q Y f).hom.hom x =
        fiberEquiv U V hU q (x ≫ f.hom) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y f x
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The correspondence is natural under actual test-cover precomposition. -/
theorem harrisIntegralCMFiniteOrbitCoverHomEquiv_naturality
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y Z : Cover T.left)
      (k : Y ⟶ Z) (f : Z ⟶ orbitCover U V hU q),
      homEquiv U V hU q Y (k ≫ f) =
        (continuousActionFunctor s hs).map k ≫ homEquiv U V hU q Z f := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y Z k f
  change (continuousActionFunctor s hs).map (k ≫ f) ≫ (orbitIso U V hU q).hom =
    (continuousActionFunctor s hs).map k ≫
      (continuousActionFunctor s hs).map f ≫ (orbitIso U V hU q).hom
  rw [Functor.map_comp, Category.assoc]

local notation "coverMap" =>
  harrisIntegralCMFiniteOrbitCoverMap
    D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The correspondence is natural under the prescribed maps of actual orbit actions. -/
theorem harrisIntegralCMFiniteOrbitCoverHomEquiv_postcomp
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z) (Y : Cover T.left)
      (k : Y ⟶ orbitCover U V hU q)
      (f : orbitAction U V hU q ⟶ orbitAction U Z hU r),
      homEquiv U Z hU r Y (k ≫ coverMap U V Z hU q r f) =
        homEquiv U V hU q Y k ≫ f := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r Y k f
  change (continuousActionFunctor s hs).map (k ≫ coverMap U V Z hU q r f) ≫
    (orbitIso U Z hU r).hom =
      ((continuousActionFunctor s hs).map k ≫ (orbitIso U V hU q).hom) ≫ f
  rw [Functor.map_comp, Category.assoc,
    harrisIntegralCMFiniteOrbitCoverMap_naturality, Category.assoc]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Every actual equivariant fibre function has a unique realizing morphism of covers. -/
theorem harrisIntegralCMFiniteOrbitCover_existsUnique
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (Y : Cover T.left)
      (k : Fiber s Y → MulAction.orbit Gamma q)
      (_hk : ∀ (gamma : Gamma) (x : Fiber s Y), k (gamma • x) = gamma • k x),
      ∃! f : Y ⟶ orbitCover U V hU q,
        ∀ x : Fiber s Y, fiberEquiv U V hU q (x ≫ f.hom) = k x := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q Y k hk
  let k' : (continuousActionFunctor s hs).obj Y ⟶ orbitAction U V hU q :=
    ObjectProperty.homMk
      { hom := FintypeCat.homMk k
        comm := by
          intro gamma
          apply FintypeCat.hom_ext
          exact hk gamma }
  let f := (homEquiv U V hU q Y).symm k'
  have hf : ∀ x : Fiber s Y, fiberEquiv U V hU q (x ≫ f.hom) = k x := by
    intro x
    exact congrArg (fun m : (continuousActionFunctor s hs).obj Y ⟶
      orbitAction U V hU q => m.hom.hom x) ((homEquiv U V hU q Y).apply_symm_apply k')
  refine ⟨f, hf, ?_⟩
  intro g hg
  apply (homEquiv U V hU q Y).injective
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro x
  exact (hg x).trans (hf x).symm

/-- The presheaf of equivariant geometric-fibre maps into the chosen raw finite orbit. -/
def harrisIntegralCMFiniteOrbitPresheaf
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ _q : RawOrbits V, (Cover T.left)ᵒᵖ ⥤ Type := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  exact (continuousActionFunctor s hs).op ⋙ yoneda.obj (orbitAction U V hU q)

local notation "orbitPresheaf" => harrisIntegralCMFiniteOrbitPresheaf
  D C P B W lam T a compatibility h s hs htor hu

/-- The selected cover naturally represents equivariant fibre maps into its raw orbit. -/
def harrisIntegralCMFiniteOrbitCoverRepresents
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, yoneda.obj (orbitCover U V hU q) ≅ orbitPresheaf U V hU q := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  refine NatIso.ofComponents (fun Y => Equiv.toIso (homEquiv U V hU q Y.unop)) ?_
  intro Y Z k
  apply ConcreteCategory.hom_ext
  intro f
  exact harrisIntegralCMFiniteOrbitCoverHomEquiv_naturality
    D C P B W lam T a compatibility h s hs htor hu U V hU q Z.unop Y.unop k.unop f

local notation "represents" => harrisIntegralCMFiniteOrbitCoverRepresents
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The natural representations respect every prescribed actual orbit action map. -/
theorem harrisIntegralCMFiniteOrbitCoverRepresents_naturality
    (U V Z : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (r : RawOrbits Z)
      (f : orbitAction U V hU q ⟶ orbitAction U Z hU r),
      yoneda.map (coverMap U V Z hU q r f) ≫ (represents U Z hU r).hom =
        (represents U V hU q).hom ≫
          Functor.whiskerLeft (continuousActionFunctor s hs).op (yoneda.map f) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r f
  apply NatTrans.ext
  funext Y
  apply ConcreteCategory.hom_ext
  intro k
  exact harrisIntegralCMFiniteOrbitCoverHomEquiv_postcomp
    D C P B W lam T a compatibility h s hs htor hu U V Z hU q r Y.unop k f

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
