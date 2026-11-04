import Langlands.Shimura.PEL.HarrisIntegralCMLevelPointComparison
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedFamilyBaseChange
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison

/-! # Actual restriction of raw full-order Harris levels -/

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
local notation "BD" => (AbelianScheme.baseChange T'.hom).obj B
local notation "BC" => (AbelianScheme.baseChange f.left).obj BT
local notation "WT" => W.pullback P T.hom
local notation "WD" => W.pullback P T'.hom
local notation "WC" => (WT).pullback P f.left
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "lamD" => W.pullbackMap P T'.hom WD lam
local notation "lamC" => (WT).pullbackMap P f.left WC lamT
local notation "aD" => (relativeEndRestrict B f).comp a
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "iD" => D.harrisHodgePELRationalAction C BD aD
local notation "iC" => (rationalBaseChangeEnd f.left BT).comp iT
local notation "e" => relativeIntegralActionRationalComparisonIso B
  (D.harrisHodgePELIntegralBasis C) f a
local notation "addDC" => relativeDualSchemeMapAdditivity P.preservation P.stability
  T'.left BD BC (WD).hasDual (WC).hasDual

omit [IsCMField F] [IsScalarTower ℚ F A] [QuasiSeparatedSpace T.left] in
/-- The actual direct-to-successive family comparison preserves the canonical
polarizations with multiplier one, without a pairing premise. -/
theorem harrisIntegralCMFullActionRestriction_multiple :
    IsRationalDualPullbackMultiple P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability
      (WD).hasDual (WC).hasDual (WD).geometry (WC).geometry
      (WD).inverseBundle (WD).evaluation (WC).inverseBundle (WC).evaluation
      addDC 1 (RationalAlgebraAction.underlyingIso e).hom
      (homToHom0 lamD) (homToHom0 lamC) := by
  change rationalDualPullbackHom0 P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability
      (WD).hasDual (WC).hasDual (WD).geometry (WC).geometry
      (WD).inverseBundle (WD).evaluation (WC).inverseBundle (WC).evaluation
      addDC (homToHom0 (relativeBaseChangeComparisonIso B f).hom)
      (homToHom0 lamC) = (1 : ℚ) • homToHom0 lamD
  rw [one_smul, rationalDualPullbackHom0_homToHom0]
  apply congrArg homToHom0
  simpa only [integralDualPullbackHom, DualWitness.pullbackMap,
    DualWitness.baseChangeIso, dualAbelianBaseChangeMap, Category.assoc] using
    dualAbelianBaseChangeMap_relative_comp_pullback P.preservation P.stability
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry
      P.universality P.compatibility B W.hasDual W.geometry W.inverseBundle W.evaluation
      f (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
      (WD).hasDual (WD).geometry (WD).inverseBundle (WD).evaluation
      (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation lam

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

/-- The canonical actual family isomorphism compares the whole raw level towers,
retaining every original Harris transporter. -/
def harrisIntegralCMFullActionRestrictionLevelIso : rawD ≅ rawC :=
  Functor.isoWhiskerLeft (hodgeLevelFunctor D C)
    (Tate.weilAdelicCompactOpenLevelIsogeny P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      (WD).hasDual (WD).geometry (WD).inverseBundle (WD).evaluation lamD
      (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation lamC
      addDC compatibility h iD iC A (D.harrisHodgePELForm C) t ht htor huD
      1 (RationalAlgebraAction.underlyingIso e)
      (RationalAlgebraAction.intertwines (e).hom)
      (harrisIntegralCMFullActionRestriction_multiple D C P B W lam f a))

local notation "compare" => harrisIntegralCMFullActionRestrictionLevelIso
  D C P B W lam f a compatibility h t ht htor huD

/-- Pull back actual fixed Weil orbits to the original direct test family.
The target action is exactly relativeEndRestrict of the supplied action. -/
def harrisIntegralCMFullActionLevelRestriction : rawT ⟶ rawD :=
  Functor.whiskerLeft (hodgeLevelFunctor D C)
    (Tate.weilAdelicCompactOpenLevelBaseChange f.left BT
      P.preservation P.composition P.unitCoherence P.associativity P.comparison
      P.symmetry P.stability P.universality
      (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
      (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation
      compatibility lamT h iT A (D.harrisHodgePELForm C) t ht hs htor huT huD) ≫
    (compare).inv

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
