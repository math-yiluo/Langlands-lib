import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedPowerModel
import Langlands.Shimura.PEL.HarrisTaylorCMRigidityReduction
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeProof

/-! # Geometric finite-order reduction for the original CM rigidity target -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)

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
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "P" => (show Prerequisites.{0} from
  { preservation := preservation
    composition := composition
    unitCoherence := unitCoherence
    associativity := associativity
    comparison := comparison
    symmetry := symmetry
    stability := stability
    square := square
    universality := universality
    compatibility := dualAbelianBaseChange
    polarizationBaseChange := polarizationBaseChange })

local notation "FiniteOrder" =>
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (B : AbelianScheme (Spec (CommRingCat.of Ω)))
    (W : DualWitness B) (lam : B ⟶ W.dual P), W.IsPolarization P lam →
      ∀ g : Aut B, g.hom ≫ lam ≫ W.map P W g.hom = lam → IsOfFinOrder g)

local notation "PrimeFaithful" =>
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (B : AbelianScheme (Spec (CommRingCat.of Ω))) (l : ℕ) [Fact l.Prime],
      Function.Injective (PrimeAdic.rationalHomMap (A := B) (B := B)
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) l))

/-- The exact original rigidity target follows from the two outstanding
geometric inputs on actual abelian schemes and their actual Tate modules. -/
def CMRigidityFromIntegralPolarizedAutomorphismsStatement : Prop :=
  FiniteOrder → PrimeFaithful →
    CMSmallLevelRigidityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor

/-- The admission fields supply the actual polarized integral power model;
only the geometric finite-order theorem is left as a premise. -/
theorem cmSmallLevelFiniteOrder_of_integralPolarizedAutomorphisms
    (hfinite : FiniteOrder) :
    CMSmallLevelFiniteOrderStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor := by
  intro U _hsmall Ω _ _ p hp
  let : ∀ k : Index (fun _ => True),
      IsFinite (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muFinite
  let : ∀ k : Index (fun _ => True),
      Etale (mu (Spec (CommRingCat.of Ω)) k.val).X.hom := hp.muEtale
  let φ : F →+* Ω := ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop ≫
    (Scheme.ΓSpecIso (.of Ω)).hom).hom
  let : CharZero Ω := charZero_of_injective_ringHom φ.injective
  let := auxiliaryStarRing D C
  intro X _hX _hnX a q e he hfixed
  apply finiteOrder_of_polarizedIntegralPowerModelWitness
    D C P compatibility h Ω X (hfinite Ω) q e
  exact polarizedIntegralPowerModelWitness_of_levelIso_fixed
    D C P compatibility h Ω
    (HarrisGeometricPoint.mk Ω (𝟙 _)).finiteFibers htor hp.torsionUnits
    X hp.pairAdditivity hp.dualExists U a q e he hfixed

/-- Composition with the proved prime-operator reduction reaches the unchanged
rigidity proposition, while retaining the two explicit geometric premises. -/
theorem cmRigidityFromIntegralPolarizedAutomorphisms :
    CMRigidityFromIntegralPolarizedAutomorphismsStatement D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality compatibility h htor := by
  intro hfinite hfaith
  exact cmSmallLevelRigidity_of_finiteOrder_and_primeFaithfulness
    D C preservation composition unitCoherence associativity comparison symmetry
    stability square universality compatibility h htor
    (cmSmallLevelFiniteOrder_of_integralPolarizedAutomorphisms D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality compatibility h htor hfinite)
    hfaith

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
