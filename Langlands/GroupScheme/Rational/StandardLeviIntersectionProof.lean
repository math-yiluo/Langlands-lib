import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof

/-! # Proof of nested standard Levi intersections and the rational radical product -/

universe u

namespace Langlands.GroupScheme

/-- For a maximal split torus of a connected reductive group over any field, a
generic cocharacter and simple-root subsets `J ⊆ K`, the subgroup `L_K ∩ U_J` is a
normal complement to `L_J` in `L_K ∩ P_J` on every test scheme, and
`U_J(k) = (L_K(k) ∩ U_J(k)) U_K(k)` on rational points. -/
theorem standardLeviIntersection : StandardLeviIntersectionStatement.{u} := by
  have hStandard : StandardCocharacterStatement.{u} :=
    standardCocharacterStatement_of_reflections_of_signs
      (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
      relativeRootSignsDetermineDynamic
  have hOrder : StandardParabolicOrderStatement.{u} := by
    intro k _ G hG T i hi ν
    have := hG.isAffineHom
    have := hi.isSplitSubtorus.mono
    intro hν
    exact standardParabolic_order_of_root_comparison i ν hν
      (relativeRootNegation k G hG T i hi)
      (fun J hJ => (hStandard k G hG T i hi ν hν J hJ).1)
      (fun zeta eta => (relativeRootSignInclusions k G hG T i hi zeta eta).1)
      (fun zeta eta => (relativeRootSignInclusions k G hG T i hi zeta eta).2)
  exact standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder
    hStandard hOrder

end Langlands.GroupScheme
