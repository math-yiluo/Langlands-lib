import Langlands.Representation.Aubert.SupportSign
import Langlands.Representation.Aubert.GradedOperatorComparison

/-!
# The actual support-adjusted Aubert operator and the full Zelevinsky comparison

This layer specializes the graded constructions to the actual support-adjusted
operator. Its proposition targets concern every actual graded class, including
rank zero. Representation-theoretic prerequisites remain explicitly named.
-/

noncomputable section

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Canonical graded additive extension of the actual rankwise adjusted operator. -/
def gradedAdjustedOperator :
    letI := T.topology
    GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  gradedOperator F T (adjustedOperator.{uF, uV} F T)

@[simp]
theorem gradedAdjustedOperator_homogeneous (n : ℕ) :
    letI := T.topology
    ∀ x, gradedAdjustedOperator F T (gradedInclusion F T n x) =
      gradedInclusion F T n (adjustedOperator F T n x) := by
  let := T.topology
  exact gradedOperator_homogeneous F T (adjustedOperator F T) n

/-- The degree-zero identity preserves the actual graded induction unit. -/
theorem gradedAdjustedOperator_unit :
    letI := T.topology
    gradedAdjustedOperator F T (gradedUnit F T) = gradedUnit F T := by
  let := T.topology
  change gradedOperator F T (adjustedOperator F T)
    (gradedInclusion F T 0 _) = gradedInclusion F T 0 _
  rw [gradedOperator_homogeneous, adjustedOperator_rankZero]
  rfl

/-- The missing actual homogeneous induction-product compatibility. -/
def AdjustedHomogeneousMultiplicativityStatement
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) : Prop :=
  HomogeneousOperatorMultiplicativityStatement F T (adjustedOperator F T) hx

/-- Multiplicativity of the actual adjusted operator on every graded class. -/
def AdjustedMultiplicativityStatement
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) : Prop :=
  GradedOperatorMultiplicativityStatement F T (adjustedOperator F T) hx

/-- The actual adjusted segment exchange, stated for the identified actual classes. -/
def AdjustedSegmentExchangeStatement : Prop :=
  GradedOperatorSegmentExchangeStatement.{uF, uV} F T (adjustedOperator F T)

/-- Involutivity of the actual graded adjusted additive operator. -/
def AdjustedInvolutivityStatement : Prop :=
  letI := T.topology
  Function.Involutive (gradedAdjustedOperator.{uF, uV} F T)

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (hp : SegmentPolynomialComparisonStatement F T hx hl)

/-- Equality of additive maps on the whole actual graded K0, not only on segments. -/
def AubertZelevinskyComparisonStatement : Prop :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  gradedAdjustedOperator F T =
    (zelevinskyEndomorphism F T hx hl hp).toAddMonoidHom.toIntLinearMap

/-- The actual adjusted ring endomorphism, once multiplicativity is proved. -/
def adjustedRingEndomorphism (hm : AdjustedMultiplicativityStatement F T hx) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  gradedOperatorRingHom F T (adjustedOperator F T) hx hl hm
    (gradedAdjustedOperator_unit F T)

/-- The corresponding whole-ring equality of actual ring endomorphisms. -/
def AubertZelevinskyRingComparisonStatement
    (hm : AdjustedMultiplicativityStatement F T hx) : Prop :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  adjustedRingEndomorphism F T hx hl hm = zelevinskyEndomorphism F T hx hl hp

/-- Comparison with the constructed Zelevinsky ring involution, as additive maps. -/
def AubertZelevinskyInvolutionComparisonStatement
    (hi : ZelevinskyInvolutivityStatement F T hx hl hp) : Prop :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  gradedAdjustedOperator F T =
    (zelevinskyRingInvolution F T hx hl hp hi).toAddEquiv.toIntLinearEquiv.toLinearMap

/-- Full Theorem 2.3 target: multiplicativity, actual whole-ring equality and
involutivity of the constructed Zelevinsky endomorphism, with every lower
exactness, ring-law and polynomial-comparison prerequisite named explicitly. -/
def AubertTheorem23Statement : Prop :=
  AdjustedMultiplicativityStatement F T hx ∧
    ZelevinskyInvolutivityStatement F T hx hl hp ∧
      AubertZelevinskyComparisonStatement F T hx hl hp

end Langlands.Aubert
