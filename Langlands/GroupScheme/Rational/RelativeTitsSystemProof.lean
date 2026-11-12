import Langlands.GroupScheme.Rational.RelativeTitsGeometricReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RationalBruhatProof

/-! # Proof: the relative Tits system of a connected reductive group -/

universe u

namespace Langlands.GroupScheme

/-- **The relative Tits system** (Borel–Tits 5.15–5.16 and 5.18, Renard V.4.1): the exact
published statement `RelativeTitsSystemStatement`, at an arbitrary universe. -/
theorem relativeTitsSystem : RelativeTitsSystemStatement.{u} :=
  relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization rationalBruhat.{u}
    rootRankOneFactorization.{u}

end Langlands.GroupScheme
