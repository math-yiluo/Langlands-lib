import Langlands.Shimura.PEL.HarrisIntegralCMLevelClassBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedFamilyBaseChange

/-! # Base naturality of actual integral Harris compatible families -/

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

local notation "aD" => (relativeEndRestrict B f).comp a

variable
    [ConnectedSpace T.left] [ConnectedSpace T'.left]
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian T'.left]
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (htor : TorsionFiniteEtaleStatement.{0})
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]
    (p : S ⟶ Spec (.of F)) (hLam : W.IsPolarization P lam)
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
    (lieT : LieBaseChangeNaturalityStatement T.left)
    (addT : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := T.left))
    (addD : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := T'.left))

local notation "PointD" => HarrisTaylorCMWeilLevel.HarrisGeometricPoint T'.left
local notation "haD" => harrisIntegralCMFullActionCondition_restrict D C P p B W lam f a ha
local notation "restrictionAt" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam f a compatibility h
local notation "toFamilyT" => harrisIntegralCMFullActionLevelFamilyNatTrans
  D C P p B W lam hLam T a ha compatibility h htor huT addT
local notation "toFamilyD" => harrisIntegralCMFullActionLevelFamilyNatTrans
  D C P p B W lam hLam T' aD haD compatibility h htor huD addD
local notation "evaluateD" => HarrisTaylorCMWeilLevel.geometricFamilyEvaluationIso
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality (T'.hom ≫ p) compatibility h
  htor huD addD
local notation "baseTriangle" => show f.left ≫ (T.hom ≫ p) = T'.hom ≫ p by
  rw [← Category.assoc, Over.w f]
local notation "familyPullWith" => HarrisTaylorCMWeilLevel.geometricFamilyTowerPullback
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality dualityNaturality
  P.polarizationBaseChange compatibility h htor f.left (T.hom ≫ p) (T'.hom ≫ p)
  baseTriangle lieT huT huD

/-- Restrict the actual raw orbit and extend its normalized class to all geometric points. -/
def harrisIntegralCMFullActionLevelFamilyRestriction
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) (v : PointD) :=
  Functor.whiskerRight
    (restrictionAt v.hom v.finiteFibers (v.comp f.left).finiteFibers htor huT huD)
    uliftFunctor.{1} ≫ toFamilyD hdim v

local notation "restrictFamily" => harrisIntegralCMFullActionLevelFamilyRestriction
  D C P B W lam f a compatibility h htor huT huD p hLam ha addD

omit [ConnectedSpace T.left] [IsLocallyNoetherian T.left] in
/-- Evaluation of the restricted compatible family is the original restricted class. -/
theorem harrisIntegralCMFullActionLevelFamilyRestriction_evaluate
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) (v : PointD) :
    restrictFamily hdim v ≫ (evaluateD v).hom =
      harrisIntegralCMFullActionLevelOriginalClassRestriction
        D C P B W lam f a compatibility h v.hom v.finiteFibers
        (v.comp f.left).finiteFibers htor huT huD p hLam ha addD hdim := by
  unfold harrisIntegralCMFullActionLevelFamilyRestriction
    harrisIntegralCMFullActionLevelOriginalClassRestriction
  rw [Category.assoc, harrisIntegralCMFullActionLevelFamilyNatTrans_evaluate]

/-- Actual level restriction commutes with unpointed compatible-family pullback,
for any constrained pulled dual data on the actual ordinary base-changed families. -/
theorem harrisIntegralCMFullActionLevelFamilyNatTrans_baseChange
    (dualData : ∀ X : PositivePolarizedAction D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
      P.universality (S := T.left),
      PositivePullbackDualData D C P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability P.square
        P.universality f.left X)
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) (v : PointD) :
    restrictFamily hdim v =
      toFamilyT hdim (v.comp f.left) ≫ familyPullWith dualData addT addD := by
  apply (cancel_mono (evaluateD v).hom).1
  rw [harrisIntegralCMFullActionLevelFamilyRestriction_evaluate, Category.assoc,
    HarrisTaylorCMWeilLevel.geometricFamilyTowerPullback_evaluation,
    ← Category.assoc, harrisIntegralCMFullActionLevelFamilyNatTrans_evaluate]
  exact harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange_dualData
    D C P B W lam f a compatibility h v.hom v.finiteFibers
    (v.comp f.left).finiteFibers htor huT huD p hLam ha
    dualityNaturality addD lieT addT dualData hdim

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
