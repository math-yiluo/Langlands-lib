import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverPointComparison

/-! # Canonical comparison of equal Harris monodromy orbit-cover choices -/

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

/-- The identity on raw classes identifies actions selected by equal orbits. -/
private def orbitActionEqIso
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q r : RawOrbits V), MulAction.orbit Gamma q = MulAction.orbit Gamma r →
      (orbitAction U V hU q ≅ orbitAction U V hU r) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr
  let e : MulAction.orbit Gamma q ≃ MulAction.orbit Gamma r :=
    { toFun := fun x => ⟨x.val, by rw [← hqr]; exact x.property⟩
      invFun := fun x => ⟨x.val, by rw [hqr]; exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e) ?_)
  intro g
  apply FintypeCat.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- The canonical isomorphism of original covers selected by equal raw orbits. -/
def harrisIntegralCMFiniteOrbitCoverOrbitEqIso
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q r : RawOrbits V), MulAction.orbit Gamma q = MulAction.orbit Gamma r →
      (orbitCover U V hU q ≅ orbitCover U V hU r) := by
  letI : MulAction Hᵐᵒᵖ Frame := rightAction
  letI : MulAction Gamma Frame := monodromyAction
  letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  letI : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  intro q r hqr
  exact (continuousActionFunctor s hs).inv.mapIso
    (orbitActionEqIso D C P B W lam T a compatibility h s hs htor hu U V hU q r hqr)

local notation "orbitEqIso" => harrisIntegralCMFiniteOrbitCoverOrbitEqIso
  D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Canonical orbit-choice comparison preserves every original raw fibre value. -/
theorem harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q r : RawOrbits V) (hqr : MulAction.orbit Gamma q = MulAction.orbit Gamma r)
      (x : Fiber s (orbitCover U V hU q)),
      (fiberEquiv U V hU r (x ≫ (orbitEqIso U V hU q r hqr).hom.hom)).val =
        (fiberEquiv U V hU q x).val := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr x
  exact congrArg Subtype.val (harrisIntegralCMFiniteOrbitCoverMap_fiber
    D C P B W lam T a compatibility h s hs htor hu U V V hU q r
    (orbitActionEqIso D C P B W lam T a compatibility h s hs htor hu U V hU q r hqr).hom x)

private theorem coverHom_ext
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ X) (ht : ∀ Y : Cover X, Finite (Fiber t Y))
    {Y Z : Cover X} (f g : Y ⟶ Z)
    (hfg : ∀ x : Fiber t Y, x ≫ f.hom = x ≫ g.hom) : f = g := by
  let : (continuousActionFunctor t ht).IsEquivalence :=
    geometricContinuousActionEquivalence t ht
  apply (continuousActionFunctor t ht).map_injective
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro x
  exact hfg x

private def orbitCoverRaw
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, Fiber s (orbitCover U V hU q) → RawOrbits V := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  exact fun q x => (fiberEquiv U V hU q x).val

local notation "rawEval" => orbitCoverRaw D C P B W lam T a compatibility h s hs htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem orbitCoverRaw_injective
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, Function.Injective (rawEval U V hU q) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q x y hxy
  exact (fiberEquiv U V hU q).injective (Subtype.ext hxy)

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem orbitCoverRaw_smul
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q : RawOrbits V) (g : Gamma) (x : Fiber s (orbitCover U V hU q)),
      rawEval U V hU q (g • x) = g • rawEval U V hU q x := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q g x
  exact congrArg Subtype.val (harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul
    D C P B W lam T a compatibility h s hs htor hu U V hU q g x)

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem orbitCoverOrbitEqIso_eval
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q r : RawOrbits V) (hqr : MulAction.orbit Gamma q = MulAction.orbit Gamma r)
      (x : Fiber s (orbitCover U V hU q)),
      rawEval U V hU r (x ≫ (orbitEqIso U V hU q r hqr).hom.hom) =
        rawEval U V hU q x := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  exact harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw
    D C P B W lam T a compatibility h s hs htor hu U V hU

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Comparing an orbit choice with itself gives the identity isomorphism. -/
theorem harrisIntegralCMFiniteOrbitCoverOrbitEqIso_refl
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ q : RawOrbits V, orbitEqIso U V hU q q rfl = Iso.refl _ := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q
  apply Iso.ext
  apply coverHom_ext s hs
  intro x
  apply (fiberEquiv U V hU q).injective
  apply Subtype.ext
  simpa using harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw
    D C P B W lam T a compatibility h s hs htor hu U V hU q q rfl x

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Canonical comparisons compose through any third choice of the same orbit. -/
theorem harrisIntegralCMFiniteOrbitCoverOrbitEqIso_trans
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q r t : RawOrbits V)
      (hqr : MulAction.orbit Gamma q = MulAction.orbit Gamma r)
      (hrt : MulAction.orbit Gamma r = MulAction.orbit Gamma t),
      orbitEqIso U V hU q r hqr ≪≫ orbitEqIso U V hU r t hrt =
        orbitEqIso U V hU q t (hqr.trans hrt) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r t hqr hrt
  apply Iso.ext
  apply coverHom_ext s hs
  intro x
  apply (fiberEquiv U V hU t).injective
  apply Subtype.ext
  change (fiberEquiv U V hU t
      ((x ≫ (orbitEqIso U V hU q r hqr).hom.hom) ≫
        (orbitEqIso U V hU r t hrt).hom.hom)).val =
    (fiberEquiv U V hU t
      (x ≫ (orbitEqIso U V hU q t (hqr.trans hrt)).hom.hom)).val
  rw [harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw,
    harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw,
    harrisIntegralCMFiniteOrbitCoverOrbitEqIso_raw]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Reversing an orbit-choice comparison gives its inverse. -/
theorem harrisIntegralCMFiniteOrbitCoverOrbitEqIso_symm
    (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Gamma Frame := monodromyAction
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    ∀ (q r : RawOrbits V) (hqr : MulAction.orbit Gamma q = MulAction.orbit Gamma r),
      (orbitEqIso U V hU q r hqr).symm = orbitEqIso U V hU r q hqr.symm := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Gamma Frame := monodromyAction
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  intro q r hqr
  apply Iso.ext
  apply (cancel_epi (orbitEqIso U V hU q r hqr).hom).mp
  have hc := congrArg Iso.hom
    (harrisIntegralCMFiniteOrbitCoverOrbitEqIso_trans
      D C P B W lam T a compatibility h s hs htor hu U V hU q r q hqr hqr.symm)
  simpa [harrisIntegralCMFiniteOrbitCoverOrbitEqIso_refl] using hc.symm

private theorem path_naturality
    {X : Scheme.{0}} {K K' : Type} [Field K] [Field K']
    {t : Spec (.of K) ⟶ X} {u : Spec (.of K') ⟶ X}
    {ht : ∀ Y : Cover X, Finite (Fiber t Y)}
    {hu : ∀ Y : Cover X, Finite (Fiber u Y)}
    (path : fiberFunctor t ht ≅ fiberFunctor u hu)
    {Y Z : Cover X} (f : Y ⟶ Z) (x : Fiber t Y) :
    path.hom.app Z (x ≫ f.hom) = path.hom.app Y x ≫ f.hom :=
  ConcreteCategory.congr_hom (path.hom.naturality f) x

private theorem path_change_apply
    {X : Scheme.{0}} {K K' : Type} [Field K] [Field K']
    {t : Spec (.of K) ⟶ X} {u : Spec (.of K') ⟶ X}
    {ht : ∀ Y : Cover X, Finite (Fiber t Y)}
    {hu : ∀ Y : Cover X, Finite (Fiber u Y)}
    (path path' : fiberFunctor t ht ≅ fiberFunctor u hu)
    (Y : Cover X) (x : Fiber t Y) :
    path'.hom.app Y x =
      (show FundamentalGroup u hu from path.symm ≪≫ path') • path.hom.app Y x := by
  change path'.hom.app Y x =
    path'.hom.app Y (path.inv.app Y (path.hom.app Y x))
  rw [show path.inv.app Y (path.hom.app Y x) = x from
    ConcreteCategory.congr_hom (path.hom_inv_id_app Y) x]

private theorem path_change_eval
    {X : Scheme.{0}} {K K' : Type} [Field K] [Field K']
    {t : Spec (.of K) ⟶ X} {u : Spec (.of K') ⟶ X}
    {ht : ∀ Y : Cover X, Finite (Fiber t Y)}
    {hu : ∀ Y : Cover X, Finite (Fiber u Y)}
    (path path' : fiberFunctor t ht ≅ fiberFunctor u hu)
    (Z : Cover X) {Qr : Type} [MulAction (FundamentalGroup u hu) Qr]
    (er : Fiber u Z → Qr)
    (hsmul : ∀ (g : FundamentalGroup u hu) (z : Fiber u Z),
      er (g • z) = g • er z) (y : Fiber t Z) :
    er (path'.hom.app Z y) =
      (show FundamentalGroup u hu from path.symm ≪≫ path') • er (path.hom.app Z y) := by
  rw [path_change_apply path path', hsmul]

private theorem path_composition_eval
    {X : Scheme.{0}} {K K' : Type} [Field K] [Field K']
    {t : Spec (.of K) ⟶ X} {u : Spec (.of K') ⟶ X}
    {ht : ∀ Y : Cover X, Finite (Fiber t Y)}
    {hu : ∀ Y : Cover X, Finite (Fiber u Y)}
    (path : fiberFunctor t ht ≅ fiberFunctor u hu)
    {Y Z Z' : Cover X} (f : Y ⟶ Z) (j : Z ⟶ Z') {Q : Type}
    (er : Fiber u Z → Q) (er' : Fiber u Z' → Q)
    (hj : ∀ z, er' (z ≫ j.hom) = er z) (R : Fiber t Y → Q)
    (hf : ∀ x, er (path.hom.app Z (x ≫ f.hom)) = R x) :
    ∀ x, er' (path.hom.app Z' (x ≫ (f ≫ j).hom)) = R x := by
  intro x
  change er' (path.hom.app Z' ((x ≫ f.hom) ≫ j.hom)) = R x
  rw [path_naturality path j, hj, hf]

private theorem coverHom_ext_raw
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {K K' : Type} [Field K] [IsAlgClosed K] [Field K']
    {t : Spec (.of K) ⟶ X} {u : Spec (.of K') ⟶ X}
    {ht : ∀ Y : Cover X, Finite (Fiber t Y)}
    {hu : ∀ Y : Cover X, Finite (Fiber u Y)}
    (path : fiberFunctor t ht ≅ fiberFunctor u hu)
    {Y Z : Cover X} (f g : Y ⟶ Z) {Q : Type}
    (ev : Fiber u Z → Q) (hinj : Function.Injective ev)
    (hev : ∀ x, ev (path.hom.app Z (x ≫ f.hom)) =
      ev (path.hom.app Z (x ≫ g.hom))) : f = g := by
  apply coverHom_ext t ht
  intro x
  apply (FintypeCat.equivEquivIso.symm (path.app Z)).injective
  exact hinj (hev x)

section PathIndependence

variable {Ω' : Type} [Field Ω'] [IsAlgClosed Ω']
    {r : Spec (.of Ω') ⟶ T.left}
    (hr : ∀ Y : Cover T.left, Finite (Fiber r Y))

local notation "FrameR" => harrisIntegralCMWeilFrame D C P B W lam T a compatibility h r
local notation "rightR" =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
    (D.harrisHodgePELForm C) r
local notation "RawR" V => @RightOrbit H _ FrameR rightR (levelSubgroup V)
local notation "GammaR" => FundamentalGroup r hr
local notation "monR" =>
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C)
    r hr htor hu
local notation "commR" =>
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (WT).hasDual (WT).geometry
    (WT).inverseBundle (WT).evaluation lamT h iT A (D.harrisHodgePELForm C)
    r hr htor hu
local notation "rawPath" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor hs hr hu
local notation "targetNonempty" => harrisIntegralCMFullActionLevelPointNonempty
  D C P B W lam T a compatibility h htor hs hr hu
local notation "coverPath" => harrisIntegralCMFiniteOrbitCoverPointIso
  D C P B W lam T a compatibility h htor hs hr hu
local notation "coverR" => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h r hr htor hu
local notation "fiberR" => harrisIntegralCMFiniteOrbitCoverFiberEquiv
  D C P B W lam T a compatibility h r hr htor hu
local notation "orbitEqR" => harrisIntegralCMFiniteOrbitCoverOrbitEqIso
  D C P B W lam T a compatibility h r hr htor hu
local notation "orbitPathEq" => harrisIntegralCMWeilRawPointEquiv_orbit_path_independent
  D C P B W lam T a compatibility h htor hs hr hu
local notation "rawEvalR" => orbitCoverRaw D C P B W lam T a compatibility h r hr htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem orbitCoverPointIso_eval
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Hᵐᵒᵖ FrameR := rightR
    letI : MulAction Gamma Frame := monodromyAction
    letI : MulAction GammaR FrameR := monR
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    letI : SMulCommClass GammaR Hᵐᵒᵖ FrameR := commR
    ∀ (q : RawOrbits V) (x : Fiber s (orbitCover U V hU q)),
      rawEvalR U V (targetNonempty path U hU) (rawPath path (levelSubgroup V) q)
          (path.hom.app _ (x ≫ (coverPath path U V hU q).hom.hom)) =
        rawPath path (levelSubgroup V) (rawEval U V hU q x) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Hᵐᵒᵖ FrameR := rightR
  let : MulAction Gamma Frame := monodromyAction
  let : MulAction GammaR FrameR := monR
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : SMulCommClass GammaR Hᵐᵒᵖ FrameR := commR
  exact harrisIntegralCMFiniteOrbitCoverPointIso_raw
    D C P B W lam T a compatibility h htor hs hr hu path U V hU

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem orbitCoverPointIso_change_eval
    (path path' : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Hᵐᵒᵖ FrameR := rightR
    letI : MulAction Gamma Frame := monodromyAction
    letI : MulAction GammaR FrameR := monR
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    letI : SMulCommClass GammaR Hᵐᵒᵖ FrameR := commR
    ∀ (q : RawOrbits V) (x : Fiber s (orbitCover U V hU q)),
      rawEvalR U V (targetNonempty path U hU) (rawPath path (levelSubgroup V) q)
          (path'.hom.app _ (x ≫ (coverPath path U V hU q).hom.hom)) =
        rawPath path' (levelSubgroup V) (rawEval U V hU q x) := by
  let : MulAction Hᵐᵒᵖ Frame := rightAction
  let : MulAction Hᵐᵒᵖ FrameR := rightR
  let : MulAction Gamma Frame := monodromyAction
  let : MulAction GammaR FrameR := monR
  let : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
  let : SMulCommClass GammaR Hᵐᵒᵖ FrameR := commR
  intro q x
  let g : GammaR := path.symm ≪≫ path'
  calc
    _ = g • rawEvalR U V (targetNonempty path U hU)
        (rawPath path (levelSubgroup V) q)
        (path.hom.app _ (x ≫ (coverPath path U V hU q).hom.hom)) :=
      path_change_eval path path' _ _
        (orbitCoverRaw_smul D C P B W lam T a compatibility h r hr htor hu U V
          (targetNonempty path U hU) (rawPath path (levelSubgroup V) q)) _
    _ = g • (show RawR V from rawPath path (levelSubgroup V) (rawEval U V hU q x)) :=
      congrArg (fun z : RawR V => g • z) (orbitCoverPointIso_eval
        D C P B W lam T a compatibility h s hs htor hu hr path U V hU q x)
    _ = rawPath path' (levelSubgroup V) (rawEval U V hU q x) :=
      (harrisIntegralCMWeilRawPointEquiv_change_path
        D C P B W lam T a compatibility h htor hs hr hu path path' (levelSubgroup V) _).symm

omit [IsCMField F] [IsScalarTower ℚ F A] in
private theorem orbitCoverPointIso_comp_eval
    (path path' : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Hᵐᵒᵖ FrameR := rightR
    letI : MulAction Gamma Frame := monodromyAction
    letI : MulAction GammaR FrameR := monR
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    letI : SMulCommClass GammaR Hᵐᵒᵖ FrameR := commR
    ∀ (q : RawOrbits V) (x : Fiber s (orbitCover U V hU q)),
      rawEvalR U V (targetNonempty path U hU) (rawPath path' (levelSubgroup V) q)
          (path'.hom.app _ (x ≫ ((coverPath path U V hU q).hom ≫
            (orbitEqR U V (targetNonempty path U hU)
              (rawPath path (levelSubgroup V) q) (rawPath path' (levelSubgroup V) q)
              (orbitPathEq path' path (levelSubgroup V) q)).hom).hom)) =
        rawPath path' (levelSubgroup V) (rawEval U V hU q x) := by
  intro q
  exact path_composition_eval path' (coverPath path U V hU q).hom
    (orbitEqR U V (targetNonempty path U hU)
      (rawPath path (levelSubgroup V) q) (rawPath path' (levelSubgroup V) q)
      (orbitPathEq path' path (levelSubgroup V) q)).hom
    (rawEvalR U V (targetNonempty path U hU) (rawPath path (levelSubgroup V) q))
    (rawEvalR U V (targetNonempty path U hU) (rawPath path' (levelSubgroup V) q))
    (orbitCoverOrbitEqIso_eval D C P B W lam T a compatibility h r hr htor hu U V
      (targetNonempty path U hU) (rawPath path (levelSubgroup V) q)
      (rawPath path' (levelSubgroup V) q) (orbitPathEq path' path (levelSubgroup V) q))
    (fun x => rawPath path' (levelSubgroup V) (rawEval U V hU q x))
    (orbitCoverPointIso_change_eval
      D C P B W lam T a compatibility h s hs htor hu hr path path' U V hU q)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- After canonical comparison of their target orbit choices, the actual cover
point isomorphisms agree for any two supplied paths. -/
theorem harrisIntegralCMFiniteOrbitCoverPointIso_path_independent
    (path path' : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U)) :
    letI : MulAction Hᵐᵒᵖ Frame := rightAction
    letI : MulAction Hᵐᵒᵖ FrameR := rightR
    letI : MulAction Gamma Frame := monodromyAction
    letI : MulAction GammaR FrameR := monR
    letI : SMulCommClass Gamma Hᵐᵒᵖ Frame := actionsComm
    letI : SMulCommClass GammaR Hᵐᵒᵖ FrameR := commR
    ∀ q : RawOrbits V,
      (coverPath path U V hU q).hom ≫
        (orbitEqR U V (targetNonempty path U hU)
          (rawPath path (levelSubgroup V) q) (rawPath path' (levelSubgroup V) q)
          (orbitPathEq path' path (levelSubgroup V) q)).hom =
      (coverPath path' U V hU q).hom := by
  intro q
  apply coverHom_ext_raw path'
    ((coverPath path U V hU q).hom ≫
      (orbitEqR U V (targetNonempty path U hU)
        (rawPath path (levelSubgroup V) q) (rawPath path' (levelSubgroup V) q)
        (orbitPathEq path' path (levelSubgroup V) q)).hom)
    (coverPath path' U V hU q).hom
    (rawEvalR U V (targetNonempty path U hU) (rawPath path' (levelSubgroup V) q))
    (orbitCoverRaw_injective D C P B W lam T a compatibility h r hr htor hu U V
      (targetNonempty path U hU) (rawPath path' (levelSubgroup V) q))
  intro x
  exact (orbitCoverPointIso_comp_eval
    D C P B W lam T a compatibility h s hs htor hu hr path path' U V hU q x).trans
    (orbitCoverPointIso_eval
      D C P B W lam T a compatibility h s hs htor hu hr path' U V hU q x).symm

end PathIndependence

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
