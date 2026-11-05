import Langlands.Shimura.PEL.HarrisIntegralCMRestrictionFrames
import Langlands.Shimura.PEL.HarrisIntegralCMLevelPointComparison
import Langlands.AbelianScheme.Tate.WeilPathBaseChange

/-! # Point comparison for original Harris raw restriction -/

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

section Points

variable {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ T.left} {r : Spec (.of Ω') ⟶ T.left}
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (hr : ∀ Y : Cover T.left, Finite (Fiber r Y))
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

/-- Actual path transport on all original raw Harris right-orbit classes.
Unlike fixed-level transport, this equivalence retains its path. -/
def harrisIntegralCMWeilRawPointEquiv
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U : Subgroup H) :
    RawAt T a s U ≃ RawAt T a r U := by
  let := rightAt T a s
  let := rightAt T a r
  exact RightOrbit.equiv U ((framePathAt T a hu) path)
    (Tate.weilAdelicFrameTransport_right P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability compatibility
      rationalWeilGeometricTransport
      (W.pullback P T.hom).hasDual (W.pullback P T.hom).geometry
      (W.pullback P T.hom).inverseBundle (W.pullback P T.hom).evaluation
      (W.pullbackMap P T.hom (W.pullback P T.hom) lam) h
      (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange T.hom).obj B) a)
      A (D.harrisHodgePELForm C) htor hu path)

local notation "rawPath" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor hs hr hu

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On an actual frame representative, the map is the original Tate path map. -/
theorem harrisIntegralCMWeilRawPointEquiv_mk
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U : Subgroup H) :
    letI := rightAt T a s
    letI := rightAt T a r
    ∀ eta : FrameAt T a s,
      rawPath path U (RightOrbit.mk U eta) =
        RightOrbit.mk U ((framePathAt T a hu) path eta) := by
  let := rightAt T a s
  let := rightAt T a r
  intro eta
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The existing path-independent original fixed-level comparison has precisely
this underlying raw-orbit map. -/
theorem harrisIntegralCMFullActionLevelPointIso_raw
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (V : HarrisLevel D)
    (l : (harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj V) :
    ((harrisIntegralCMFullActionLevelPointIso
      D C P B W lam T a compatibility h htor hu path).hom.app V l).val =
      rawPath path ((hodgeLevelFunctor D C).obj V).subgroup l.val := rfl

end Points

section Restriction

variable {T' : Over S} [QuasiSeparatedSpace T'.left] (f : T' ⟶ T)
    {Ω Ω' : Type} [Field Ω] [Field Ω']
    (t : Spec (.of Ω) ⟶ T'.left) (u : Spec (.of Ω') ⟶ T'.left)
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (hupt : ∀ Y : Cover T'.left, Finite (Fiber u Y))
    (htf : ∀ Y : Cover T.left, Finite (Fiber (t ≫ f.left) Y))
    (huf : ∀ Y : Cover T.left, Finite (Fiber (u ≫ f.left) Y))
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "aD" => (relativeEndRestrict B f).comp a
local notation "frameEval" => harrisIntegralCMRestrictionFrameEquiv
  D C P B W lam f a compatibility h

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual restriction evaluation commutes with arbitrary fibre-functor paths
on the test and their pushed paths on the base. Endpoint fields may differ. -/
theorem harrisIntegralCMRestrictionFrameEquiv_pointMap
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (eta : FrameAt T' aD t) :
    frameEval u ((framePathAt T' aD huD) path eta) =
      (framePathAt T a huT) (pathPushforward f.left htf huf path) (frameEval t eta) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [harrisIntegralCMRestrictionFrameEquiv_apply,
    Tate.weilAdelicFrameTransport_apply,
    Tate.weilAdelicFrameTransport_apply,
    harrisIntegralCMRestrictionFrameEquiv_apply]
  rw [← Tate.rationalTransport_homMap htor (fun _ => True) huD
    (homToHom0 (relativeBaseChangeComparisonIso B f).hom) path]
  exact Tate.rationalBaseChange_transport f.left htf huf htor
    ((AbelianScheme.baseChange T.hom).obj B) (fun _ => True) huT huD path
    (Tate.rationalHomMap (Over.mk t) (fun _ => True)
      (homToHom0 (relativeBaseChangeComparisonIso B f).hom) (eta.1 x))

local notation "rawEval" => harrisIntegralCMRestrictionRawEquiv
  D C P B W lam f a compatibility h
local notation "rawPathD" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T' aD compatibility h htor ht hupt huD
local notation "rawPathT" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor htf huf huT

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The actual raw evaluation square for arbitrary endpoint fields is induced
by the actual frame square, without a fixedness hypothesis on its input. -/
theorem harrisIntegralCMRestrictionRawEquiv_pointMap
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt)
    (U : Subgroup H) (q : RawAt T' aD t U) :
    rawEval u U (rawPathD path U q) =
      rawPathT (pathPushforward f.left htf huf path) U (rawEval t U q) := by
  let := rightAt T a (u ≫ f.left)
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (harrisIntegralCMRestrictionFrameEquiv_pointMap D C P B W lam T a
        compatibility h htor f t u ht hupt htf huf huT huD path eta)

local notation "levelDAt" t₀:max ht₀:max =>
  harrisIntegralCMFullActionLevelTower
    D C P B W lam T' aD compatibility h t₀ ht₀ htor huD
local notation "levelTAt" s₀:max hs₀:max =>
  harrisIntegralCMFullActionLevelTower
    D C P B W lam T a compatibility h s₀ hs₀ htor huT
local notation "pointD" => harrisIntegralCMFullActionLevelPointIso
  D C P B W lam T' aD compatibility h htor huD
local notation "pointT" => harrisIntegralCMFullActionLevelPointIso
  D C P B W lam T a compatibility h htor huT
local notation "evalAt" t₀:max ht₀:max hs₀:max =>
  harrisIntegralCMRestrictionRawClass
    D C P B W lam f a compatibility h t₀ ht₀ htor huD
    (t₀ ≫ f.left) rfl hs₀
local notation "restrictAt" t₀:max ht₀:max hs₀:max =>
  harrisIntegralCMFullActionLevelRestriction
    D C P B W lam f a compatibility h t₀ ht₀ hs₀ htor huT huD

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original fixed-level point transport commutes with original raw evaluation
at the two induced base points. -/
theorem harrisIntegralCMRestrictionRawClass_pointMap
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt)
    (V : HarrisLevel D) (l : (levelDAt t ht).obj V) :
    (evalAt u hupt huf) V ((pointD path).hom.app V l) =
      rawPathT (pathPushforward f.left htf huf path)
        ((hodgeLevelFunctor D C).obj V).subgroup ((evalAt t ht htf) V l) := by
  rw [harrisIntegralCMRestrictionRawClass_eq_rawEquiv,
    harrisIntegralCMFullActionLevelPointIso_raw,
    harrisIntegralCMRestrictionRawClass_eq_rawEquiv]
  exact harrisIntegralCMRestrictionRawEquiv_pointMap D C P B W lam T a
    compatibility h htor f t u ht hupt htf huf huT huD path _ l.val

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The unchanged original fixed-level restriction commutes with arbitrary
point paths and their actual pushforward. -/
theorem harrisIntegralCMFullActionLevelRestriction_pointMap
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt)
    (V : HarrisLevel D) (l : (levelTAt (t ≫ f.left) htf).obj V) :
    (restrictAt u hupt huf).app V
        ((pointT (pathPushforward f.left htf huf path)).hom.app V l) =
      (pointD path).hom.app V ((restrictAt t ht htf).app V l) := by
  apply Subtype.ext
  apply (rawEval u ((hodgeLevelFunctor D C).obj V).subgroup).injective
  rw [harrisIntegralCMFullActionLevelRestriction_rawValue,
    harrisIntegralCMFullActionLevelPointIso_raw,
    harrisIntegralCMFullActionLevelPointIso_raw,
    harrisIntegralCMRestrictionRawEquiv_pointMap,
    harrisIntegralCMFullActionLevelRestriction_rawValue]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The point-comparison and actual restriction square commutes as a square of
natural transformations over all original Harris level transporters. -/
theorem harrisIntegralCMFullActionLevelRestriction_point_naturality
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) :
    (pointT (pathPushforward f.left htf huf path)).hom ≫
        restrictAt u hupt huf =
      restrictAt t ht htf ≫ (pointD path).hom := by
  ext V l
  exact harrisIntegralCMFullActionLevelRestriction_pointMap D C P B W lam T a
    compatibility h htor f t u ht hupt htf huf huT huD path V l

end Restriction
end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
