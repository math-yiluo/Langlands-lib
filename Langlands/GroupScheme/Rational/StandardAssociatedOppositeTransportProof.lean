import Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportReduction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Associated standard groups and ambient opposite groups: proof -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- For a lift `n` of the longest representative `longestRep cs J` and a standard cocharacter
`zeta` for `J`, conjugation by `n` carries the associated standard parabolic and radical onto
the dynamic opposite parabolic and radical of `zeta`. -/
theorem standardAssociatedOppositeTransport : StandardAssociatedOppositeTransportStatement.{u} :=
  standardAssociatedOppositeTransport_of_relativeRootNegation relativeRootNegation

end Langlands.GroupScheme
