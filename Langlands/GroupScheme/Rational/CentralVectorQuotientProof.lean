import Langlands.GroupScheme.Rational.CentralVectorQuotientReduction
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationProof
import Langlands.GroupScheme.Rational.CommutativePTorsionVectorProof
import Langlands.GroupScheme.Rational.SplitTorusVectorLinearizationProof

/-! # Central stable vector subgroups and smooth unipotent quotients -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- The two characteristic cases of commutative vector classification. -/
theorem commutativeVectorClassification : CommutativeVectorClassificationStatement.{u} :=
  ⟨commutativeUnipotentVectorCharZero, smoothCommutativePTorsionVector⟩

/-- The exact central stable vector-subgroup target over algebraically closed fields. -/
theorem centralStableVectorSubgroup : CentralStableVectorSubgroupStatement.{u} :=
  centralStableVectorSubgroup_of_vectorInputs
    commutativeVectorClassification splitTorusVectorLinearization

/-- The exact central-vector and quotient prerequisites for dimension induction. -/
theorem centralVectorQuotient : CentralVectorQuotientStatement.{u} :=
  ⟨centralStableVectorSubgroup, centralSmoothQuotient⟩

end Langlands.GroupScheme.RelativeRoot
