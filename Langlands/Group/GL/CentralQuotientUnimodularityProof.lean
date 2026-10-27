import Langlands.Group.GL.CentralQuotientUnimodularityStatement
import Langlands.Group.GL.CentralQuotientMeasure

/-! # Right invariance of Haar measures on actual p-adic GL central quotients -/

namespace Langlands

universe uF

/-- Every Haar measure on the actual full central quotient of a positive-rank
p-adic general linear group is right invariant for the supplied topology. -/
theorem glCentralQuotientHaarRightInvariant :
    GLCentralQuotientHaarRightInvariantStatement.{uF} := by
  intro p _ F T
  let := T.topology
  intro n _
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro μ _
  exact T.centralQuotientHaar_rightInvariant n μ

end Langlands
