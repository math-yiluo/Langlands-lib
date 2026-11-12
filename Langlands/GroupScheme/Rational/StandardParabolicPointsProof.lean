import Langlands.GroupScheme.Rational.StandardParabolicTitsRealizationOfStatements
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.StandardCocharacterReduction
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeTitsGeometricReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RationalBruhatProof

/-! # Proof: standard parabolics on rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The order on standard parabolics, from the relative root system: the root system gives
standard cocharacters, and the published root-sign comparisons give the dynamic inclusions. -/
theorem standardParabolicOrder_of_relativeRootSystem
    (hroot : RelativeRootSystemStatement.{u}) : StandardParabolicOrderStatement.{u} := by
  have hstd := standardCocharacterStatement_of_relativeRootSystem_of_signs hroot
    relativeRootSignsDetermineDynamic
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  exact standardParabolic_order_of_root_comparison i ν hν
    (relativeRootNegation k G hG T i hi)
    (fun J hJ => (hstd k G hG T i hi ν hν J hJ).1)
    (fun z e => (relativeRootSignInclusions k G hG T i hi z e).1)
    (fun z e => (relativeRootSignInclusions k G hG T i hi z e).2)

/-- The four standard-parabolic clauses from the rational Bruhat decomposition and actual
rank-one factorization, through the relative Tits system, the Coxeter realization of the
relative Weyl group and the order on standard parabolics. -/
theorem standardParabolicPointsStatement_of_bruhat_and_rankOneFactorization
    (hBr : RationalBruhatStatement.{u}) (hRank : RootRankOneFactorizationStatement.{u}) :
    StandardParabolicPointsStatement.{u} := by
  have hroot := relativeRootSystemStatement_of_rootRankOneFactorizationStatement hRank
  have hstruct : RootGeneratedCentralizerStructuralPremises.{u} := ⟨hroot, hRank⟩
  exact standardParabolicPointsStatement_of_titsRealization
    (standardParabolicTitsRealization_of_statements
      (relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization hBr hRank)
      (standardRelativeWeylGenerationStatement_of_relativeWeylCoxeter
        hstruct.relativeWeylCoxeter))
    standardParabolicEndpoints (standardParabolicOrder_of_relativeRootSystem hroot)

/-- **Standard parabolics on rational points** (Borel–Tits 5.17, 5.18, 5.20): the exact
published statement `StandardParabolicPointsStatement`, at an arbitrary universe. -/
theorem standardParabolicPointsStatement_proof : StandardParabolicPointsStatement.{u} :=
  standardParabolicPointsStatement_of_bruhat_and_rankOneFactorization rationalBruhat
    rootRankOneFactorization

end Langlands.GroupScheme
