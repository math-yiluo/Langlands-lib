import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetFactorTarget
import Langlands.Representation.Aubert.General.PrerequisiteStatements

/-! # Reductions of Sharp finite length and of zero and exactness detection

Three implication statements between published targets on the actual rational
points. Each one says that a target with no published reduction follows from
named published targets. No proof is supplied here.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Reduction of finite length of the actual terminal cokernel `E#` (the
derived input of Aubert 1995, Corollaire 3.9 (a)) on the actual rational-point
families to the two dynamic finite-length targets (Renard VI.6.2 and VI.6.4)
at the carrier universe `max (u + 1) v`. No proof is supplied. -/
def RationalSharpFiniteLengthReductionStatement : Prop :=
  DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
    DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
      RationalSharpFiniteLengthStatement.{u, v}

/-- Reduction of zero detection on the actual support categories `Alg({I})`
(Aubert 1996 erratum, first sentence of the corrected proof, for one object)
to extraction of cuspidal Jacquet factors from subquotients of actual
parabolic inductions on the actual rational-point families. No proof is
supplied. -/
def RationalSupportCategoryZeroDetectionReductionStatement : Prop :=
  RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
    RationalSupportCategoryZeroDetectionStatement.{u, v}

/-- Reduction of exactness detection on the actual support categories
`Alg({I})` (Aubert 1996 erratum, first sentence of the corrected proof) to
zero detection on the same categories. No proof is supplied. -/
def RationalSupportCategoryExactnessDetectionReductionStatement : Prop :=
  RationalSupportCategoryZeroDetectionStatement.{u, v} →
    RationalSupportCategoryExactnessDetectionStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
