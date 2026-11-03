import Langlands.Shimura.PEL.HarrisIntegralCMFullActionLocus
import Langlands.Shimura.PEL.HarrisAdelicFrameFaithfulness
import Langlands.Shimura.PEL.PolarizedWeilIntegralClasses
import Langlands.Shimura.PEL.HarrisTaylorCMCentralTrace

/-! # Actual polarized CM actions from the integral joint condition -/

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

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
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
      CategoryTheory.End ((baseChange T.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ T.left)

local notation "BT" => Functor.obj (baseChange T.hom) B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "Af" => Global.FiniteAdeles ℚ

variable (heta : Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  Tate.AdelicFrame ((baseChange T.hom).obj B) h
    (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a)
    ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) s))

/-- The same actual pulled-back family and map form a faithful polarized action.
Only faithfulness uses the existence of the actual pointed Harris frame. -/
def harrisIntegralCMFullActionPolarizedAction :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.PolarizedAction P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      T.left A := by
  letI := auxiliaryStarRing D C
  have hfaith : Function.Injective iT := by
    exact heta.elim (fun eta => action_injective_of_adelicFrame D C BT h iT s eta)
  exact {
    actionObj := RationalAlgebraAction.of BT iT
    hasDual := (WT).hasDual
    geometry := (WT).geometry
    inversePoincare := (WT).inverseBundle
    evaluation := (WT).evaluation
    dualEndAdditivity := relativeDualSchemeMapAdditivity P.preservation P.stability
      T.left BT BT (WT).hasDual (WT).hasDual
    polarization := lamT
    isPolarization := P.polarizationBaseChange P.preservation P.square P.universality
      P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry
      P.compatibility S T.left T.hom B W.hasDual W.geometry W.inverseBundle W.evaluation
      (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation lam hLam
    faithful := hfaith
    involutionCompatible :=
      (harrisIntegralCMFullActionCondition_involutionCompatible
        D C P p B W lam T a ha).1 }

local notation "X" => harrisIntegralCMFullActionPolarizedAction
  D C P p B W lam hLam T a ha h s heta

/-- The assembly retains the literal rational extension of the original integral action. -/
@[simp] theorem harrisIntegralCMFullActionPolarizedAction_action :
    letI := auxiliaryStarRing D C
    (X).actionObj.action = iT := rfl

/-- The actual polarization is the canonical pullback of the original fixed map. -/
@[simp] theorem harrisIntegralCMFullActionPolarizedAction_polarization :
    letI := auxiliaryStarRing D C
    (X).polarization = lamT := rfl

/-- The original actual integral action is an integral restriction on this same
polarized family; no new integral model or isogeny is chosen. -/
def harrisIntegralCMFullActionPolarizedRestriction :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality (D.harrisHodgePELIntegralOrder C) X := by
  letI := auxiliaryStarRing D C
  exact ⟨a, fun x => (D.harrisHodgePELRationalAction_coe C BT a x).symm⟩

/-- The ambient prescribed dimension supplies precisely the missing numerical
conjunct of the unchanged normalized CM condition. -/
theorem harrisIntegralCMFullActionPolarizedAction_determinantDimension
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C (T.hom ≫ p)
      (X).actionObj.abelianScheme (X).actionObj.action := by
  let _ := auxiliaryStarRing D C
  exact ⟨ha.2, HarrisTaylor.prescribedRelativeDimension_baseChange E B n hdim T.hom⟩

section Locus

open Langlands.GroupScheme.Cartier

variable [IsLocallyNoetherian S] (R : Over S)
    [LocallyOfFiniteType R.hom] [IsSeparated R.hom]
    (eR : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj R)

local notation "raw" => (relativeIntegralActionLocusTest R B
  (D.harrisHodgePELIntegralBasis C) eR).obj

variable
    (H : Over (relativeIntegralActionLocusTest R B
      (D.harrisHodgePELIntegralBasis C) eR).obj.left) [IsSeparated H.hom]
    (eH : (locallyNoetherianTestInclusion
        (relativeIntegralActionLocusTest R B (D.harrisHodgePELIntegralBasis C) eR).obj.left).op ⋙
        relativeHomFunctor
          ((baseChange (relativeIntegralActionLocusTest R B
            (D.harrisHodgePELIntegralBasis C) eR).obj.hom).obj B).toCommGroupScheme
          ((W.pullback P (relativeIntegralActionLocusTest R B
            (D.harrisHodgePELIntegralBasis C) eR).obj.hom).dual P).toCommGroupScheme ⋙
          forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion
        (relativeIntegralActionLocusTest R B (D.harrisHodgePELIntegralBasis C) eR).obj.left).op ⋙
        yoneda.obj H)
    (Q : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))

local instance locusTest_isLocallyNoetherian : IsLocallyNoetherian Q.obj.left := Q.property

local notation "Z" => harrisIntegralCMActionLocus D C P p B W lam R eR H eH

variable (k : Q.obj ⟶ harrisIntegralCMActionLocus D C P p B W lam R eR H eH)
    (sQ : Spec (.of Ω) ⟶ Q.obj.left)
    (hetaQ : Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Tate.AdelicFrame ((baseChange Q.obj.hom).obj B) h
        (D.harrisHodgePELRationalAction C ((baseChange Q.obj.hom).obj B)
          (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH Q k).val)
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) sQ))

local notation "aQ" => (harrisIntegralCMFullActionLocusHomEquiv
  D C P p B W lam R eR H eH Q k).val

/-- A morphism into the actual joint locus yields a faithful polarized action
on the original direct test family when its actual Harris frame exists. -/
def harrisIntegralCMActionLocusPolarizedAction :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.PolarizedAction P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Q.obj.left A :=
  harrisIntegralCMFullActionPolarizedAction D C P p B W lam hLam Q.obj aQ
    (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH Q k).property
    h sQ hetaQ

local notation "XQ" => harrisIntegralCMActionLocusPolarizedAction
  D C P p B W lam hLam h R eR H eH Q k sQ hetaQ

/-- The classified polarized action uses exactly the rational extension of the
literal restriction of the raw universal integral action. -/
@[simp] theorem harrisIntegralCMActionLocusPolarizedAction_action :
    letI := auxiliaryStarRing D C
    (XQ).actionObj.action = D.harrisHodgePELRationalAction C
      ((baseChange Q.obj.hom).obj B)
      ((relativeEndRestrict B
          (k ≫ harrisIntegralCMActionLocusInclusion D C P p B W lam R eR H eH)).comp
        (relativeIntegralActionUniversal B (D.harrisHodgePELIntegralBasis C) R eR)) := by
  let _ := auxiliaryStarRing D C
  change D.harrisHodgePELRationalAction C ((baseChange Q.obj.hom).obj B) aQ = _
  rw [harrisIntegralCMFullActionLocusHomEquiv_apply]

/-- The actual integral restriction is the action classified by the same map. -/
def harrisIntegralCMActionLocusPolarizedRestriction :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality (D.harrisHodgePELIntegralOrder C) XQ :=
  harrisIntegralCMFullActionPolarizedRestriction D C P p B W lam hLam Q.obj aQ
    (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH Q k).property
    h sQ hetaQ

/-- The unchanged normalized CM numerical condition holds for every such
classifying map from an ambient family of the prescribed dimension. -/
theorem harrisIntegralCMActionLocusPolarizedAction_determinantDimension
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C (Q.obj.hom ≫ p)
      (XQ).actionObj.abelianScheme (XQ).actionObj.action :=
  harrisIntegralCMFullActionPolarizedAction_determinantDimension D C P p B W lam hLam
    Q.obj aQ
    (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH Q k).property
    h sQ hetaQ hdim

end Locus

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
