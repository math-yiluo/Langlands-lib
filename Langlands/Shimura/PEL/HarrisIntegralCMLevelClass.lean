import Langlands.Shimura.PEL.HarrisIntegralCMPolarizedAction
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClassImage

/-! # Raw fixed Weil levels give the original normalized integral CM classes -/

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
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P) (hLam : W.IsPolarization P lam)
    (T : Over S) [QuasiSeparatedSpace T.left]
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ T.left)
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a

/-- The actual fixed Weil-level tower on the direct integral-action family.
Its definition does not require an already faithful polarized action. -/
def harrisIntegralCMFullActionLevelTower : HarrisLevel D ⥤ Type :=
  hodgeLevelFunctor D C ⋙
    Tate.weilAdelicCompactOpenLevelTower P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability compatibility
      (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation lamT
      h iT A (D.harrisHodgePELForm C) s hs htor hu

local notation "rawTower" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h s hs htor hu

/-- Existence of an actual fixed orbit implies existence of an actual ambient
Harris frame. No representative is required to be monodromy fixed. -/
theorem harrisIntegralCMFullActionLevel_nonemptyFrame {U : HarrisLevel D}
    (q : (harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U) :
    Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Tate.AdelicFrame BT h iT ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) s) := by
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  obtain ⟨eta, _⟩ := Quotient.exists_rep q.val
  exact ⟨eta.1⟩

/-- The supplied actual orbit and its original family form actual faithful
polarized Harris level data. Faithfulness is derived from that same orbit. -/
def harrisIntegralCMFullActionLevelData {U : HarrisLevel D}
    (q : (harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U) :
    HarrisLevelData D C P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability P.square P.universality
      compatibility h s hs htor hu U := by
  letI := auxiliaryStarRing D C
  exact ⟨harrisIntegralCMFullActionPolarizedAction D C P p B W lam hLam T a ha h s
    (harrisIntegralCMFullActionLevel_nonemptyFrame
      D C P B W lam T a compatibility h s hs htor hu q), q⟩

local notation "levelData" => harrisIntegralCMFullActionLevelData
  D C P p B W lam hLam T a ha compatibility h s hs htor hu

/-- This representative uses the literal original integral action, polarization
and orbit and has the unchanged normalized determinant and dimension. -/
def harrisIntegralCMFullActionLevelRepresentative
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    {U : HarrisLevel D}
    (q : (harrisIntegralCMFullActionLevelTower
      D C P B W lam T a compatibility h s hs htor hu).obj U) :
    HarrisTaylorCMWeilLevel.IntegralCMRepresentative D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
      P.universality (T.hom ≫ p) compatibility h s hs htor hu U := by
  letI := auxiliaryStarRing D C
  exact {
    data := levelData q
    condition := harrisIntegralCMFullActionPolarizedAction_determinantDimension
      D C P p B W lam hLam T a ha h s
      (harrisIntegralCMFullActionLevel_nonemptyFrame
        D C P B W lam T a compatibility h s hs htor hu q) hdim
    restriction := harrisIntegralCMFullActionPolarizedRestriction
      D C P p B W lam hLam T a ha h s
      (harrisIntegralCMFullActionLevel_nonemptyFrame
        D C P B W lam T a compatibility h s hs htor hu q) }

local notation "representative" => harrisIntegralCMFullActionLevelRepresentative
  D C P p B W lam hLam T a ha compatibility h s hs htor hu

/-- The full original transporter category acts on the supplied orbit, keeping
the actual integral-action representative. -/
theorem harrisIntegralCMFullActionLevelRepresentative_map
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    {U V : HarrisLevel D} (f : U ⟶ V) (q : (rawTower).obj U) :
    representative hdim ((rawTower).map f q) =
      HarrisTaylorCMWeilLevel.integralCMRepresentativeMap D C P.preservation
        P.composition P.unitCoherence P.associativity P.comparison P.symmetry
        P.stability P.square P.universality (T.hom ≫ p) compatibility
        h s hs htor hu f (representative hdim q) := rfl

variable
    (additivity : PositivePairAdditivity D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality (S := T.left))

/-- Actual fixed Weil levels on a joint integral family give original integral
CM isogeny classes, naturally for every original Harris transporter. -/
def harrisIntegralCMFullActionLevelClassNatTrans
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) :
    rawTower ⋙ uliftFunctor.{1} ⟶
      HarrisTaylorCMWeilLevel.integralCMClassTower D C P.preservation P.composition
        P.unitCoherence P.associativity P.comparison P.symmetry P.stability
        P.square P.universality (T.hom ≫ p) compatibility h s hs htor hu additivity where
  app _ := ↾(fun q => HarrisTaylorCMWeilLevel.integralCMClassOf D C
    P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility
    h s hs htor hu additivity (representative hdim q.down))
  naturality := by
    intro U V f
    ext q
    rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
