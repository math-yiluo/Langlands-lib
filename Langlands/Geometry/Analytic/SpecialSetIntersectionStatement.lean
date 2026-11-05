import Langlands.Geometry.Analytic.SpecialChartCover
import Langlands.Geometry.Analytic.AtlasDomainCategory

/-! # The special-set full local-domain intersection target -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

/-- Berkovich's special-set intersection lemma is stated on the full
local-domain enlargement of the original net. The intersection and the
admissibility of its genuine completed-tensor map are conclusions. -/
def SpecialSetIntersectionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : Type v) [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
    (W : Set X), a.IsSpecialSet W →
    ∀ U V : LocalDomain a, U.locus ⊆ W → V.locus ⊆ W →
      ∃ R : LocalDomain a, ∃ hR : R.locus = U.locus ∩ V.locus,
        (CompletedTensorAlgebra.lift
          (LocalDomain.Inclusion.ofSubset R U (by
            intro x hx
            have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
            exact hx'.1)).restriction
          (LocalDomain.Inclusion.ofSubset R V (by
            intro x hx
            have hx' : x ∈ U.locus ∩ V.locus := hR ▸ hx
            exact hx'.2)).restriction).IsAdmissibleEpi

end Langlands.Analytic.IndexedAffinoidAtlas
