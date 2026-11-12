import Langlands.Representation.Classification.RegularLanglandsStatement
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof
import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageProof

/-!
# Exhaustion by regular tempered Langlands heads

Independent tempered quotient coverage supplies a standard module surjecting
onto the given input. Its strong head identifies the kernels of all irreducible
quotient maps, so this very input is also its strong head.
-/

namespace Langlands

universe uF uV

/-- Every irreducible admissible smooth representation of positive-rank
`GL_n(F)` is the strong head of an actual regular tempered standard module. -/
theorem glRegularLanglandsExhaustion :
    GLRegularLanglandsExhaustionStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn π hπ _hπadm
  obtain ⟨d, _, q, hq⟩ :=
    Classification.temperedLanglandsQuotientCoverage.{uF, uV} F T n hn π hπ
  obtain ⟨τ, _, r, hr, hker⟩ :=
    glRegularLanglandsHeadExistence.{uF, uV} p F T n hn d
  refine ⟨d, hπ, q, hq, ?_⟩
  intro W _ _ σ hσ s hs
  exact (hker W σ hσ s hs).trans (hker π π.representation hπ q hq).symm

end Langlands
