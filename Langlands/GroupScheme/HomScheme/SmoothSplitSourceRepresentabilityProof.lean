import Langlands.GroupScheme.HomScheme.GraphLocusUniversal
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof

/-! # Smooth representability of actual Hom from a split torus -/

universe u

namespace Langlands.GroupScheme.HomScheme

/-- The actual relative Hom presheaf from a split torus to a smooth affine group scheme
over any base scheme is represented by a smooth scheme over that base. -/
theorem smoothSplitSourceRepresentability :
    SmoothSplitSourceRepresentabilityStatement.{u} :=
  smoothSplitSourceRepresentability_of_torusSubgroupModuli
    TorusSubgroupModuli.smoothTorusSubgroupRepresentability.{u}

end Langlands.GroupScheme.HomScheme
