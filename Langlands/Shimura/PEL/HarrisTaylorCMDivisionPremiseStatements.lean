import Langlands.Shimura.PEL.HarrisTaylorCMDivisionCriteria

/-! # The three division-case premises of CM representability as closed statements -/

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

/-- Division-case quasi-projective representability: if the algebra is a
division algebra, then at every small level the existing normalized class
presheaf is represented, on the componentwise admissible test category, by a
scheme over `Spec F` with an immersion into a finite projective space over
`F`. No smoothness, properness or admissibility of the scheme is asked. -/
def DivisionCMQuasiProjectiveRepresentabilityStatement : Prop :=
  D.IsDivision → ∀ U : SmallCMLevel D, Nonempty
    (CMLevelQuasiProjectiveRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U)

/-- Division-case infinitesimal lifting: if the algebra is a division algebra,
then at every small level, normalized classes over `Spec B` lift to `Spec B'`
along every surjection `B' → B` of local Artinian rings whose kernel is killed
by the maximal ideal of `B'`, for every structure morphism `Spec B' ⟶ Spec F`. -/
def DivisionCMArtinianLiftingStatement : Prop :=
  D.IsDivision → ∀ U : SmallCMLevel D,
    CMLevelArtinianLiftingStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U

/-- Division-case extension over discrete valuation rings: if the algebra is a
division algebra, then at every small level, normalized classes over the
fraction field `K` of a discrete valuation ring `V` extend over `Spec V`, for
every structure morphism `Spec V ⟶ Spec F`. -/
def DivisionCMDiscreteValuativeExistenceStatement : Prop :=
  D.IsDivision → ∀ U : SmallCMLevel D,
    CMLevelDiscreteValuativeExistenceStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U

/-- The division-case target follows from the three closed premise statements.
None of the three premises is proved here. -/
theorem divisionCMRepresentabilityStatement_of_premiseStatements
    (hrep : DivisionCMQuasiProjectiveRepresentabilityStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor)
    (hlift : DivisionCMArtinianLiftingStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hval : DivisionCMDiscreteValuativeExistenceStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor) :
    DivisionCMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor :=
  divisionCMRepresentabilityStatement_of_criteria hrep hlift hval

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
