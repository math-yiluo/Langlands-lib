import Langlands.Shimura.PEL.HarrisTaylorCMSchemeStabilizers
import Langlands.Shimura.PEL.HarrisTaylorCMRepresentabilityStatement

/-! # The small-level rigidity target for the normalized CM moduli problem -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

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

/-- Harris--Taylor's small-level rigidity input: at every original level
whose image in the similitude group at some finite prime has no nontrivial
element of finite order, the actual coarse-level rigidity holds at every
admitted algebraically closed field point. This is a target, not a theorem. -/
def CMSmallLevelRigidityStatement : Prop :=
  ∀ U : HarrisLevel D, D.rationalInvolution.LevelSufficientlySmall U →
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U

/-- The target supplies the rigidity premise at every object of the existing
sufficiently-small level category. -/
theorem CMSmallLevelRigidityStatement.rigid
    (r : CMSmallLevelRigidityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor)
    (U : SmallCMLevel D) :
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj :=
  r U.obj U.property

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
