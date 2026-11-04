import Langlands.Shimura.PEL.HarrisIntegralCMLevelFamilyImage

/-! # Comparison of fixed-family and arbitrary integral Harris class images -/

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
open HarrisTaylorCMWeilLevel

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

local notation "Tests" => HarrisIntegralCMTestCategory D C P p
local notation "toCM" => harrisIntegralCMTestToCMBase D C P p

variable (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P) (hLam : W.IsPolarization P lam)
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (htor : TorsionFiniteEtaleStatement.{0})
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})

local notation "family" => unpointedClassTower D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality compatibility h htor
local notation "condition" => HarrisIntegralCMLevelFamilyCondition
  D C P p B W lam hLam hdim compatibility h htor
local notation "integralCondition" => IntegralCMFamilyCondition D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality compatibility h htor
local notation "fixedPresheaf" => harrisIntegralCMLevelFamilyImagePresheaf
  D C P p B W lam hLam hdim compatibility h htor dualityNaturality
local notation "integralPresheaf" => integralCMUnpointedClassImagePresheaf
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality dualityNaturality
  P.polarizationBaseChange compatibility h htor
local notation "ambientPresheaf" => unpointedClassTowerPresheaf
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality dualityNaturality
  P.polarizationBaseChange compatibility h htor

/-- The same actual direct-family representative witnesses membership in the
existing arbitrary integral-action image at every geometric point. -/
theorem harrisIntegralCMLevelFamilyCondition_integral (T : Tests)
    {U : HarrisLevel D} (x : (family ((toCM).obj T)).obj U)
    (hx : condition T x) : integralCondition ((toCM).obj T) x := by
  obtain ⟨a, ha, hq⟩ := hx
  intro v
  obtain ⟨q, hq⟩ := hq v
  let y := harrisIntegralCMFullActionLevelRepresentative D C P p B W lam hLam
    T.obj a ha compatibility h v.hom v.finiteFibers htor
    T.property.torsionUnits hdim q
  refine ⟨y, ?_⟩
  have heval := congrArg (fun k => k.app U (ULift.up q))
    (harrisIntegralCMFullActionLevelFamilyNatTrans_evaluate D C P p B W lam
      hLam T.obj a ha compatibility h htor T.property.torsionUnits
      T.property.pairAdditivity hdim v)
  exact heval.symm.trans (congrArg (fun z => z.val v) hq)

/-- The fixed-family image factors into the existing arbitrary integral-action
image, naturally in test morphisms and every Harris level transporter. -/
def harrisIntegralCMLevelFamilyImageToIntegral :
    fixedPresheaf ⟶ (toCM).op ⋙ integralPresheaf where
  app T := {
    app _ := ↾(fun x => ⟨x.val,
      harrisIntegralCMLevelFamilyCondition_integral D C P p B W lam hLam hdim
        compatibility h htor T.unop x.val x.property⟩)
    naturality _ _ _ := rfl }
  naturality _ _ _ := rfl

/-- The factorization retains exactly the underlying original normalized class
family; composing the two inclusions is the fixed-family inclusion. -/
theorem harrisIntegralCMLevelFamilyImageToIntegral_inclusion :
    harrisIntegralCMLevelFamilyImageToIntegral D C P p B W lam hLam hdim
      compatibility h htor dualityNaturality ≫
      Functor.whiskerLeft (toCM).op
        (integralCMUnpointedClassImagePresheafInclusion D C P.preservation
          P.composition P.unitCoherence P.associativity P.comparison P.symmetry
          P.stability P.square P.universality dualityNaturality
          P.polarizationBaseChange compatibility h htor) =
    harrisIntegralCMLevelFamilyImageInclusion D C P p B W lam hLam hdim
      compatibility h htor dualityNaturality := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
