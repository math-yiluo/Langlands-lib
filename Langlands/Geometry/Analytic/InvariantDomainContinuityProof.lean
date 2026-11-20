import Langlands.Geometry.Analytic.InvariantDomainContinuityStatement
import Langlands.Geometry.Analytic.ContinuousInvariantDomain

/-! # Proof that invariant analytic domains of `G`-spaces are `G`-spaces -/

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- The restriction of the continuous action of a `G`-space to an invariant analytic domain is
continuous in Berkovich's sense. -/
theorem invariantDomainContinuity : InvariantDomainContinuityStatement.{u, v, w, z} :=
  fun _ _ _ _ _ _ _ X D hD => X.property.2.invariantDomainAction D hD

end Langlands.Analytic.SaturatedAtlasPresentation
