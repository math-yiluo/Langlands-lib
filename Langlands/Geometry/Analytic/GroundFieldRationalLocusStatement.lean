import Langlands.Geometry.Analytic.AnalyticRationalLocus
import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas

/-! # Rational points under analytic ground field extension -/

universe u v w u'

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set

/-- In the ground-field extension of an affinoid atlas, the `L`-rational points whose
projections are `K`-rational form a closed subset of the `L`-rational locus. Each
`K`-rational point has exactly one `L`-rational point above it. -/
def GroundFieldRationalLocusStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] (A : AffinoidAtlasPresentation.{u, v, w} K),
    let π := projection K L A.atlas
    let R := (presentation K L A.atlas).rationalLocus L
    let S := A.rationalLocus K
    IsClosed (Subtype.val ⁻¹' (π ⁻¹' S) : Set R) ∧
      InjOn π (R ∩ π ⁻¹' S) ∧ S ⊆ π '' R

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
