import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitPointComparison
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverMaps

/-! # Point comparison of actual finite Harris orbit covers -/

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

private def pathFiberEquiv
    {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ X} {r : Spec (.of Ω') ⟶ X}
    {hs : ∀ Y : Cover X, Finite (Fiber s Y)}
    {hr : ∀ Y : Cover X, Finite (Fiber r Y)}
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (Y : Cover X) :
    Fiber s Y ≃ Fiber r Y :=
  FintypeCat.equivEquivIso.symm (path.app Y)

private theorem pathFiberEquiv_smul
    {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ X} {r : Spec (.of Ω') ⟶ X}
    {hs : ∀ Y : Cover X, Finite (Fiber s Y)}
    {hr : ∀ Y : Cover X, Finite (Fiber r Y)}
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (Y : Cover X)
    (g : FundamentalGroup s hs) (x : Fiber s Y) :
    pathFiberEquiv path Y (g • x) =
      pathConjugation path g • pathFiberEquiv path Y x := by
  change path.hom.app Y (g.hom.app Y x) =
    path.hom.app Y (g.hom.app Y (path.inv.app Y (path.hom.app Y x)))
  have hx : path.inv.app Y (path.hom.app Y x) = x :=
    ConcreteCategory.congr_hom (path.hom_inv_id_app Y) x
  rw [hx]

private def pathCoverActionIso
    {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ X} {r : Spec (.of Ω') ⟶ X}
    {hs : ∀ Y : Cover X, Finite (Fiber s Y)}
    {hr : ∀ Y : Cover X, Finite (Fiber r Y)}
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (Y Z : Cover X)
    (e : Fiber s Y ≃ Fiber r Z)
    (he : ∀ (g : FundamentalGroup s hs) (x : Fiber s Y),
      e (g • x) = pathConjugation path g • e x) :
    (continuousActionFunctor s hs).obj Y ≅
      (continuousActionFunctor s hs).obj Z := by
  let e₀ := e.trans (pathFiberEquiv path Z).symm
  have he₀ : ∀ (g : FundamentalGroup s hs) (x : Fiber s Y),
      e₀ (g • x) = g • e₀ x := by
    intro g x
    apply (pathFiberEquiv path Z).injective
    rw [pathFiberEquiv_smul]
    change (pathFiberEquiv path Z) ((pathFiberEquiv path Z).symm (e (g • x))) =
      pathConjugation path g •
      (pathFiberEquiv path Z) ((pathFiberEquiv path Z).symm (e x))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, he]
  refine ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e₀) ?_)
  intro g
  apply FintypeCat.hom_ext
  intro x
  exact he₀ g x

private def pathCoverIso
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω Ω' : Type} [Field Ω] [Field Ω'] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} {r : Spec (.of Ω') ⟶ X}
    {hs : ∀ Y : Cover X, Finite (Fiber s Y)}
    {hr : ∀ Y : Cover X, Finite (Fiber r Y)}
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (Y Z : Cover X)
    (e : Fiber s Y ≃ Fiber r Z)
    (he : ∀ (g : FundamentalGroup s hs) (x : Fiber s Y),
      e (g • x) = pathConjugation path g • e x) : Y ≅ Z := by
  letI : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  exact (continuousActionFunctor s hs).preimageIso (pathCoverActionIso path Y Z e he)

private theorem pathCoverIso_fiber
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω Ω' : Type} [Field Ω] [Field Ω'] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} {r : Spec (.of Ω') ⟶ X}
    {hs : ∀ Y : Cover X, Finite (Fiber s Y)}
    {hr : ∀ Y : Cover X, Finite (Fiber r Y)}
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (Y Z : Cover X)
    (e : Fiber s Y ≃ Fiber r Z)
    (he : ∀ (g : FundamentalGroup s hs) (x : Fiber s Y),
      e (g • x) = pathConjugation path g • e x) (x : Fiber s Y) :
    path.hom.app Z (x ≫ (pathCoverIso path Y Z e he).hom.hom) = e x := by
  let : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  have hmap := (continuousActionFunctor s hs).map_preimage
    (pathCoverActionIso path Y Z e he).hom
  have hx := congrArg (fun k : (continuousActionFunctor s hs).obj Y ⟶
    (continuousActionFunctor s hs).obj Z => k.hom.hom x) hmap
  change x ≫ (pathCoverIso path Y Z e he).hom.hom =
    (pathFiberEquiv path Z).symm (e x) at hx
  rw [hx]
  exact (pathFiberEquiv path Z).apply_symm_apply (e x)

private theorem pathFiberEquiv_naturality
    {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ X} {r : Spec (.of Ω') ⟶ X}
    {hs : ∀ Y : Cover X, Finite (Fiber s Y)}
    {hr : ∀ Y : Cover X, Finite (Fiber r Y)}
    (path : fiberFunctor s hs ≅ fiberFunctor r hr)
    {Y Z : Cover X} (f : Y ⟶ Z) (x : Fiber s Y) :
    pathFiberEquiv path Z (x ≫ f.hom) = pathFiberEquiv path Y x ≫ f.hom :=
  ConcreteCategory.congr_hom (path.hom.naturality f) x

private theorem coverHom_ext
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (hs : ∀ Y : Cover X, Finite (Fiber s Y))
    {Y Z : Cover X} (f g : Y ⟶ Z)
    (hfg : ∀ x : Fiber s Y, x ≫ f.hom = x ≫ g.hom) : f = g := by
  let : (continuousActionFunctor s hs).IsEquivalence :=
    geometricContinuousActionEquivalence s hs
  apply (continuousActionFunctor s hs).map_injective
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  intro x
  exact hfg x

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


local notation "H" => ScalarExtensionSimilitudes A A
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

local notation "framePathAt" T₀:max a₀:max hu₀:max =>
  Tate.weilAdelicFrameTransport P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport
    (W.pullback P (T₀).hom).hasDual (W.pullback P (T₀).hom).geometry
    (W.pullback P (T₀).hom).inverseBundle (W.pullback P (T₀).hom).evaluation
    (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) htor hu₀

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
section CoverPointComparison

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [IsAlgClosed Ω] [IsAlgClosed Ω']
    [ConnectedSpace T.left] [IsLocallyNoetherian T.left]
    {s : Spec (.of Ω) ⟶ T.left} {r : Spec (.of Ω') ⟶ T.left}
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (hr : ∀ Y : Cover T.left, Finite (Fiber r Y))
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "rawPath" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor hs hr hu
local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).subgroup
local notation "GammaS" => FundamentalGroup s hs
local notation "GammaR" => FundamentalGroup r hr
local notation "levelAt" s₀:max hs₀:max => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h s₀ hs₀ htor hu
local notation "coverAt" s₀:max hs₀:max => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h s₀ hs₀ htor hu
local notation "fiberAt" s₀:max hs₀:max => harrisIntegralCMFiniteOrbitCoverFiberEquiv
  D C P B W lam T a compatibility h s₀ hs₀ htor hu
local notation "pointAt" s₀:max hs₀:max => harrisIntegralCMFiniteOrbitCoverPoint
  D C P B W lam T a compatibility h s₀ hs₀ htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] [IsAlgClosed Ω] [IsAlgClosed Ω']
  [ConnectedSpace T.left] [IsLocallyNoetherian T.left] in
/-- A source reference level gives the target reference level via original point transport. -/
theorem harrisIntegralCMFullActionLevelPointNonempty
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    Nonempty ((levelAt r hr).obj U) :=
  hU.map ((harrisIntegralCMFullActionLevelPointIso
    D C P B W lam T a compatibility h htor hu path).hom.app U)

local notation "targetNonempty" => harrisIntegralCMFullActionLevelPointNonempty
  D C P B W lam T a compatibility h htor hs hr hu

private def rawOrbitPointEquiv
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (V : HarrisLevel D) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ q : RawAt T a s (levelSubgroup V),
      MulAction.orbit GammaS q ≃
        MulAction.orbit GammaR (rawPath path (levelSubgroup V) q) := by
  letI := rightAt T a s
  letI := rightAt T a r
  letI := monAt T a s hs hu
  letI := monAt T a r hr hu
  letI := commAt T a s hs hu
  letI := commAt T a r hr hu
  intro q
  exact (rawPath path (levelSubgroup V)).subtypeEquiv
    (fun z => (harrisIntegralCMWeilRawPointEquiv_mem_orbit_iff
      D C P B W lam T a compatibility h htor hs hr hu path (levelSubgroup V) q z).symm)

/-- Compare actual cover fibres using actual raw path transport on the selected orbit. -/
def harrisIntegralCMFiniteOrbitCoverPointFiberEquiv
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ q : RawAt T a s (levelSubgroup V),
      Fiber s ((coverAt s hs) U V hU q) ≃
        Fiber r ((coverAt r hr) U V (targetNonempty path U hU)
          (rawPath path (levelSubgroup V) q)) := by
  letI := rightAt T a s
  letI := rightAt T a r
  letI := monAt T a s hs hu
  letI := monAt T a r hr hu
  letI := commAt T a s hs hu
  letI := commAt T a r hr hu
  intro q
  exact ((fiberAt s hs) U V hU q).trans
    ((rawOrbitPointEquiv D C P B W lam T a compatibility h htor hs hr hu path V q).trans
      ((fiberAt r hr) U V (targetNonempty path U hU)
        (rawPath path (levelSubgroup V) q)).symm)

local notation "fiberPath" => harrisIntegralCMFiniteOrbitCoverPointFiberEquiv
  D C P B W lam T a compatibility h htor hs hr hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The fibre comparison has exactly the original raw point-transport value. -/
theorem harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_val
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ (q : RawAt T a s (levelSubgroup V))
      (x : Fiber s ((coverAt s hs) U V hU q)),
      ((fiberAt r hr) U V (targetNonempty path U hU)
        (rawPath path (levelSubgroup V) q) (fiberPath path U V hU q x)).val =
      rawPath path (levelSubgroup V) ((fiberAt s hs) U V hU q x).val := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q x
  exact congrArg Subtype.val (((fiberAt r hr) U V (targetNonempty path U hU)
    (rawPath path (levelSubgroup V) q)).apply_symm_apply _)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual fibre comparison intertwines monodromy under actual path conjugation. -/
theorem harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_smul
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ (q : RawAt T a s (levelSubgroup V)) (g : GammaS)
      (x : Fiber s ((coverAt s hs) U V hU q)),
      fiberPath path U V hU q (g • x) =
        pathConjugation path g • fiberPath path U V hU q x := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q g x
  apply ((fiberAt r hr) U V (targetNonempty path U hU)
    (rawPath path (levelSubgroup V) q)).injective
  apply Subtype.ext
  rw [harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_val,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_smul]
  change rawPath path (levelSubgroup V)
    (g • (show RawAt T a s (levelSubgroup V) from ((fiberAt s hs) U V hU q x).val)) =
    pathConjugation path g • (show RawAt T a r (levelSubgroup V) from
      ((fiberAt r hr) U V (targetNonempty path U hU)
        (rawPath path (levelSubgroup V) q) (fiberPath path U V hU q x)).val)
  rw [harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_val]
  exact harrisIntegralCMWeilRawPointEquiv_monodromy
    D C P B W lam T a compatibility h htor hs hr hu path (levelSubgroup V) g
      ((fiberAt s hs) U V hU q x).val


/-- Compare the actual finite Harris orbit covers chosen at two geometric points. -/
def harrisIntegralCMFiniteOrbitCoverPointIso
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ q : RawAt T a s (levelSubgroup V),
      (coverAt s hs) U V hU q ≅
        (coverAt r hr) U V (targetNonempty path U hU)
          (rawPath path (levelSubgroup V) q) := by
  letI := rightAt T a s
  letI := rightAt T a r
  letI := monAt T a s hs hu
  letI := monAt T a r hr hu
  letI := commAt T a s hs hu
  letI := commAt T a r hr hu
  intro q
  exact pathCoverIso path _ _ (fiberPath path U V hU q)
    (harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_smul
      D C P B W lam T a compatibility h htor hs hr hu path U V hU q)

local notation "coverPath" => harrisIntegralCMFiniteOrbitCoverPointIso
  D C P B W lam T a compatibility h htor hs hr hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- After actual path transport, the cover isomorphism has its constructed fibre value. -/
theorem harrisIntegralCMFiniteOrbitCoverPointIso_fiber
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ (q : RawAt T a s (levelSubgroup V))
      (x : Fiber s ((coverAt s hs) U V hU q)),
      path.hom.app _ (x ≫ (coverPath path U V hU q).hom.hom) =
        fiberPath path U V hU q x := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q x
  exact pathCoverIso_fiber path _ _ (fiberPath path U V hU q)
    (harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_smul
      D C P B W lam T a compatibility h htor hs hr hu path U V hU q) x

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual cover comparison has the original raw path-transport evaluation. -/
theorem harrisIntegralCMFiniteOrbitCoverPointIso_raw
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ (q : RawAt T a s (levelSubgroup V))
      (x : Fiber s ((coverAt s hs) U V hU q)),
      ((fiberAt r hr) U V (targetNonempty path U hU)
        (rawPath path (levelSubgroup V) q)
        (path.hom.app _ (x ≫ (coverPath path U V hU q).hom.hom))).val =
      rawPath path (levelSubgroup V) ((fiberAt s hs) U V hU q x).val := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q x
  rw [harrisIntegralCMFiniteOrbitCoverPointIso_fiber]
  exact harrisIntegralCMFiniteOrbitCoverPointFiberEquiv_val
    D C P B W lam T a compatibility h htor hs hr hu path U V hU q x

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual path transport of the distinguished source lift is the distinguished target lift. -/
theorem harrisIntegralCMFiniteOrbitCoverPointIso_point
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ q : RawAt T a s (levelSubgroup V),
      path.hom.app _ ((pointAt s hs) U V hU q ≫ (coverPath path U V hU q).hom.hom) =
        (pointAt r hr) U V (targetNonempty path U hU)
          (rawPath path (levelSubgroup V) q) := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q
  apply ((fiberAt r hr) U V (targetNonempty path U hU)
    (rawPath path (levelSubgroup V) q)).injective
  apply Subtype.ext
  rw [harrisIntegralCMFiniteOrbitCoverPointIso_raw,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_point,
    harrisIntegralCMFiniteOrbitCoverFiberEquiv_point]

local notation "levelArrow" => (hodgeLevelFunctor D C).map
local notation "rawTranslate" f =>
  RightOrbit.translate (G := H) (levelArrow f).element (levelArrow f).respects
local notation "coverTransportAt" s₀:max hs₀:max => harrisIntegralCMFiniteOrbitCoverTransport
  D C P B W lam T a compatibility h s₀ hs₀ htor hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual point comparison commutes with every original Harris cover transporter. -/
theorem harrisIntegralCMFiniteOrbitCoverPointIso_naturality
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U V Z : HarrisLevel D)
    (hU : Nonempty ((levelAt s hs).obj U)) (f : V ⟶ Z) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ (q : RawAt T a s (levelSubgroup V)) (z : RawAt T a s (levelSubgroup Z))
      (hqz : (rawTranslate f) q = z),
      (coverPath path U V hU q).hom ≫
        (coverTransportAt r hr) U V Z (targetNonempty path U hU) f
          (rawPath path (levelSubgroup V) q) (rawPath path (levelSubgroup Z) z)
          (by rw [← harrisIntegralCMWeilRawPointEquiv_translate, hqz]) =
      (coverTransportAt s hs) U V Z hU f q z hqz ≫
        (coverPath path U Z hU z).hom := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q z hqz
  apply coverHom_ext s hs
  intro x
  apply (pathFiberEquiv path _).injective
  apply ((fiberAt r hr) U Z (targetNonempty path U hU)
    (rawPath path (levelSubgroup Z) z)).injective
  apply Subtype.ext
  change ((fiberAt r hr) U Z (targetNonempty path U hU)
      (rawPath path (levelSubgroup Z) z)
      (pathFiberEquiv path _ ((x ≫ (coverPath path U V hU q).hom.hom) ≫ _))).val =
    ((fiberAt r hr) U Z (targetNonempty path U hU)
      (rawPath path (levelSubgroup Z) z)
      (pathFiberEquiv path _ ((x ≫ _) ≫ (coverPath path U Z hU z).hom.hom))).val
  rw [pathFiberEquiv_naturality]
  change ((fiberAt r hr) U Z (targetNonempty path U hU)
      (rawPath path (levelSubgroup Z) z)
      (path.hom.app _ (x ≫ (coverPath path U V hU q).hom.hom) ≫ _)).val =
    ((fiberAt r hr) U Z (targetNonempty path U hU)
      (rawPath path (levelSubgroup Z) z)
      (path.hom.app _ ((x ≫ _) ≫ (coverPath path U Z hU z).hom.hom))).val
  rw [harrisIntegralCMFiniteOrbitCoverTransport_fiber,
    harrisIntegralCMFiniteOrbitCoverPointIso_raw,
    harrisIntegralCMFiniteOrbitCoverPointIso_raw,
    harrisIntegralCMFiniteOrbitCoverTransport_fiber]
  exact (harrisIntegralCMWeilRawPointEquiv_translate
    D C P B W lam T a compatibility h htor hs hr hu path
    (levelArrow f).element (levelArrow f).respects
    ((fiberAt s hs) U V hU q x).val).symm

end CoverPointComparison

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
