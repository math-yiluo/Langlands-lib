import Langlands.Representation.Classification.TemperedJointSupportStatement
import Langlands.Representation.Classification.TemperedLeviUpperSupportProof
import Langlands.Representation.Classification.DiscreteSeriesPositiveRootSupportProof
import Langlands.Representation.Classification.NestedInductionProof

/-!
# Joint fine, middle and coarse support of tempered product-Levi representations

Apply upper discrete-series support, apply positive-root cuspidal support to
the resulting middle representation, and transport the two quotient maps
through normalized induction in stages for the actual composite refinement.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Every irreducible analytically tempered product-Levi representation has
joint unitary cuspidal and square-integrable support with all three actual
surjections and the same transported fine data. -/
theorem glTemperedJointSupport :
    GLTemperedJointSupportStatement.{uF, uV} := by
  intro p hp F T n hn B π hπ hπt
  obtain ⟨Q, σ, hσ, hσsq, qMC, hqMC⟩ :=
    glTemperedLeviUpperSupport.{uF, uV} p F T n hn B π hπ hπt
  obtain ⟨R, ω, v₀, hω, hωc, hωu, hv₀, qFM, hqFM⟩ :=
    glDiscreteSeriesPositiveRootSupport.{uF, max uF uV}
      p F T n hn (B.flatten Q) σ hσ hσsq
  obtain ⟨qFC, hqFC⟩ :=
    normalizedNestedInduction.{uF, max uF uV, max uF uV, uV}.2
      p F T n B Q R ω v₀ σ π qFM qMC hqFM hqMC
  exact ⟨Q, R, B.composeRefinement Q R, B.flatten_composeRefinement Q R,
    ω, v₀, σ, hω, hωc, hωu, hv₀, hσ, hσsq,
    qFM, qMC, qFC, hqFM, hqMC, hqFC⟩

end Langlands
