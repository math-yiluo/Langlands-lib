import Langlands.BaseChange.AssociatedSphericalTwoBlockOrbitalDescent
import Langlands.BaseChange.RegularOrbitalProfileExistence
import Langlands.BaseChange.SatakeCharacter
import Langlands.BaseChange.UnramifiedBaseChangeHom
import Langlands.TraceFormula.CyclicFieldGlobalizationProof
import Langlands.TraceFormula.FundamentalLemmaGlobalizationReduction

/-! # Reduction of the spherical fundamental lemma to rational comparison and the elliptic norm criterion -/

namespace Langlands.BaseChange

open Langlands.TraceFormula

universe u v

/-- Rational spherical concordance near a regular elliptic norm pair and the
elliptic norm criterion together imply the spherical fundamental lemma. -/
def FundamentalLemmaRationalComparisonReductionStatement : Prop :=
  RationalSphericalConcordanceNearEllipticStatement.{u, v} →
  EllipticNormCriterionStatement.{u, v} →
  FundamentalLemmaStatement.{u, v}

theorem fundamentalLemmaRationalComparisonReduction :
    FundamentalLemmaRationalComparisonReductionStatement.{u, v} := by
  intro hRational hNorm
  have hElliptic : RegularEllipticFundamentalLemmaStatement.{u, v} :=
    fundamentalLemmaGlobalizationReduction cyclicFieldGlobalization
      regularOrbitalProfileExistence hRational hNorm satakeCharacter satakeCharacter
  exact fundamentalLemmaEllipticReduction hElliptic unramifiedBaseChangeHom

end Langlands.BaseChange
