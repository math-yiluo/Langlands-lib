import Langlands.Shimura.PEL.HarrisIntegralCMLevelRestriction
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralImageBaseChange

/-! # Normalized CM classes commute with actual full-order level restriction -/

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

/-- Construct dual inputs on the actual changed family from the given source dual. -/
def harrisIntegralCMLevelPullbackDualData
    (X : PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := T.left)) :
    PositivePullbackDualData D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality f.left X := by
  letI := auxiliaryStarRing D C
  let WX : DualWitness X.actionObj.abelianScheme :=
    ⟨X.hasDual, X.geometry, X.inversePoincare, X.evaluation⟩
  let WY := WX.pullback P f.left
  exact ⟨WY.hasDual, WY.geometry, WY.inverseBundle, WY.evaluation,
    relativeDualSchemeMapAdditivity P.preservation P.stability T'.left
      ((AbelianScheme.baseChange f.left).obj X.actionObj.abelianScheme)
      ((AbelianScheme.baseChange f.left).obj X.actionObj.abelianScheme)
      WY.hasDual WY.hasDual⟩

local notation "duals" => harrisIntegralCMLevelPullbackDualData D C P f
local notation "compare" => harrisIntegralCMFullActionRestrictionLevelIso
  D C P B W lam f a compatibility h t ht htor huD
local notation "restriction" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam f a compatibility h t ht hs htor huT huD
local notation "rawPull" => Functor.whiskerLeft (hodgeLevelFunctor D C)
  (Tate.weilAdelicCompactOpenLevelBaseChange f.left BT
    P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability P.universality
    (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
    (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation
    compatibility lamT h iT A (D.harrisHodgePELForm C) t ht hs htor huT huD)

variable (p : S ⟶ Spec (.of F)) (hLam : W.IsPolarization P lam)
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
    (addD : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := T'.left))

local notation "haD" => harrisIntegralCMFullActionCondition_restrict D C P p B W lam f a ha
local notation "dataT" => harrisIntegralCMFullActionLevelData D C P p B W lam hLam
  T a ha compatibility h (t ≫ f.left) hs htor huT
local notation "dataD" => harrisIntegralCMFullActionLevelData D C P p B W lam hLam
  T' aD haD compatibility h t ht htor huD
local notation "pullData" => levelDataBaseChange D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality dualityNaturality P.polarizationBaseChange f.left compatibility h
  t ht hs htor huT huD duals

/-- The actual direct restricted representative and ordinary pulled representative
are related by the canonical comparison and the original rational-isogeny relation. -/
theorem harrisIntegralCMFullActionLevelRestriction_related
    (U : HarrisLevel D) (q : (rawT).obj U) :
    letI := auxiliaryStarRing D C
    (PolarizedWeilLevel.isogenySetoid P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      compatibility h A (D.harrisHodgePELForm C) t ht htor huD addD
      ((hodgeLevelFunctor D C).obj U)).r
      (dataD ((restriction).app U q)) (pullData U (dataT q)) := by
  let := auxiliaryStarRing D C
  refine ⟨1, e, ?_, ?_⟩
  · dsimp only [PolarizedWeilLevel.Multiple, harrisIntegralCMFullActionLevelData,
      harrisIntegralCMFullActionPolarizedAction, levelDataBaseChange,
      framedPositiveActionBaseChange, harrisIntegralCMLevelPullbackDualData]
    change IsRationalDualPullbackMultiple P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability
      (WD).hasDual (WC).hasDual (WD).geometry (WC).geometry
      (WD).inverseBundle (WD).evaluation (WC).inverseBundle (WC).evaluation
      addDC 1 (RationalAlgebraAction.underlyingIso e).hom
      (homToHom0 lamD) (homToHom0 lamC)
    exact harrisIntegralCMFullActionRestriction_multiple D C P B W lam f a
  · dsimp only [harrisIntegralCMFullActionLevelData,
      harrisIntegralCMFullActionPolarizedAction, levelDataBaseChange,
      framedPositiveActionBaseChange, harrisIntegralCMLevelPullbackDualData,
      PolarizedWeilLevel.levelIso, harrisIntegralCMFullActionLevelRestriction,
      framedPositiveActionTowerBaseChange]
    have inverseLaw := ((compare).app U).inv_hom_id_apply ((rawPull).app U q)
    dsimp only [harrisIntegralCMFullActionRestrictionLevelIso,
      Tate.weilAdelicCompactOpenLevelIsogeny] at inverseLaw
    exact inverseLaw

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
