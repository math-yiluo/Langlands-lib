import Langlands.BaseChange.EllipticNormCriterion
import Langlands.BaseChange.FundamentalLemmaRationalComparisonReduction

/-! # The spherical fundamental lemma from rational spherical concordance -/

namespace Langlands.BaseChange

open Langlands.TraceFormula

universe u v

/-- Rational spherical concordance near regular elliptic norm pairs implies the
spherical fundamental lemma. -/
def FundamentalLemmaFromRationalConcordanceStatement : Prop :=
  RationalSphericalConcordanceNearEllipticStatement.{u, v} →
    FundamentalLemmaStatement.{u, v}

theorem fundamentalLemmaFromRationalConcordance :
    FundamentalLemmaFromRationalConcordanceStatement.{u, v} := by
  intro hRational
  exact fundamentalLemmaRationalComparisonReduction hRational ellipticNormCriterion

end Langlands.BaseChange
