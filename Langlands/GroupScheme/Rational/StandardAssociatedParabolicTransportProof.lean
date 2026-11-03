import Langlands.GroupScheme.Rational.StandardAssociatedConjugation

/-! # Whole standard parabolic and radical transport in associated Levis -/

universe u

namespace Langlands.GroupScheme

/-- Every longest normalizer lift transports the entire associated standard
parabolic and radical families on every test scheme. -/
theorem standardAssociatedParabolicTransport :
    StandardAssociatedParabolicTransportStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro _ _ _ CM cs h J n hn I
  exact associatedStandardSubgroups_eq_comap i ν cs h J n hn I

end Langlands.GroupScheme
