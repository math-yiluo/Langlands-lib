import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedDisconnectedPresheaf
import Langlands.Shimura.Unitary.SufficientlySmallLevels
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Yoneda

/-! # Exact representability targets for the actual normalized CM presheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

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
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality

/-- The original transporter category, restricted by the actual local smallness
condition. The translating elements of its arrows are retained. -/
abbrev SmallCMLevel := D.rationalInvolution.SmallLevelCategory

/-- The actual disconnected normalized CM presheaves, transposed in the level
variable and restricted to sufficiently small levels. -/
def smallLevelClassPresheafTower : SmallCMLevel D ⥤ DisBasesᵒᵖ ⥤ Type 1 :=
  ObjectProperty.ι D.rationalInvolution.LevelSufficientlySmall ⋙
    (disconnectedClassTowerPresheaf D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor).flip

local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Exact representing evidence at a fixed small level: an actual admissible
CM scheme, smoothness and an actual projective-space closed immersion, and a
natural isomorphism to the already constructed class presheaf. -/
structure CMLevelRepresentation (U : SmallCMLevel D) where
  base : DisBases
  smooth : Smooth base.obj.hom
  projective : IsHProjective base.obj.hom
  represents : uliftYoneda.{1}.obj base ≅ (moduli).obj U

/-- The pointwise representability target. This definition supplies no proof
and imposes no universal projectivity claim on arbitrary central simple data. -/
def CMLevelRepresentabilityStatement (U : SmallCMLevel D) : Prop :=
  Nonempty (CMLevelRepresentation D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)

/-- The exact existence obligation at every sufficiently small original level
for the particular arithmetic datum and the explicit named prerequisites. -/
def CMRepresentabilityStatement : Prop :=
  ∀ U : SmallCMLevel D,
    CMLevelRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
