import Langlands.Shimura.PEL.HarrisTaylorCMGeometricFiniteOrderReduction
import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphismFinitenessStatement
import Langlands.AbelianScheme.Tate.FieldPrimeRationalFaithfulnessProof

/-! # CM rigidity from the remaining polarized-automorphism finiteness target -/

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

/-- The exact original rigidity target now requires only the published
geometric polarized-automorphism finiteness proposition. -/
def CMRigidityFromPolarizedAutomorphismFinitenessStatement : Prop :=
  PolarizedAutomorphismFinitenessStatement.{0} →
    CMSmallLevelRigidityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor

/-- Actual one-prime faithfulness discharges the prime premise, while the
finite polarized subgroup gives finite order in the actual automorphism group. -/
theorem cmRigidityFromPolarizedAutomorphismFiniteness :
    CMRigidityFromPolarizedAutomorphismFinitenessStatement D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality compatibility h htor := by
  intro hfinite
  apply cmRigidityFromIntegralPolarizedAutomorphisms D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor
  · intro Ω _ _ _ B W lam hpol g hpres
    let K : Subgroup (Aut B) :=
      polarizedAutGroup preservation composition unitCoherence associativity comparison
        symmetry stability W.hasDual W.geometry W.inverseBundle W.evaluation lam
    have : Finite K :=
      hfinite preservation square universality composition unitCoherence associativity
        comparison symmetry stability Ω B W.hasDual W.geometry W.inverseBundle
        W.evaluation lam hpol
    let gK : K := ⟨g, hpres⟩
    obtain ⟨k, hk, hpow⟩ := (isOfFinOrder_of_finite gK).exists_pow_eq_one
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk, ?_⟩
    change (K.subtype gK) ^ k = 1
    rw [← map_pow, hpow, map_one]
  · intro Ω _ _ _ B p _
    exact fieldPrimeRationalFaithfulness Ω B B p

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
