import Langlands.Geometry.Building.IwasawaDecompositionReduction
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.RootSubgroupVectorProof

/-! # Proof of the chamber Iwasawa decomposition

KP Theorem 5.3.3, `G(F) = U(F) N(F) P_C` for a chamber `C` and the unipotent radical `U` of
the minimal parabolic of a generic cocharacter, on the actual building data. The conditional
`iwasawaDecompositionStatement_of_structuralStatements` is applied to the published proofs of
its seven algebraic premises.
-/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **KP Theorem 5.3.3 (chamber Iwasawa decomposition).** For every chamber `C` of the
apartment and every generic cocharacter `ν`, `G(F) = U(F) N(F) P_C` with
`U = standardUnipotentPoints P.i ν ∅`, under the published hypotheses. -/
theorem iwasawaDecomposition : IwasawaDecompositionStatement.{u} :=
  iwasawaDecompositionStatement_of_structuralStatements relativeWeylCoxeter
    standardParabolicEndpoints rationalBruhat rootRankOneFactorization relativeRootSystem
    RelativeRoot.dynamicRootOrderedProduct RelativeRoot.rootSubgroupVector

end Langlands.Geometry.Building
