import Langlands.Geometry.Analytic.InducedSiteEquivalence
import Langlands.Geometry.Analytic.OpenPartitionCoproduct
import Langlands.Geometry.Analytic.QuasiEtaleOpenRestrictionProof

/-! # Proof: induction on equivariant quasi-étale sites is an equivalence

Berkovich's Example 1.2.1(i), quasi-étale case. -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

/-- **Berkovich's Example 1.2.1(i), quasi-étale case.** For an open subgroup `H` of a
topological group `G` and an `H`-space `X`, induction `Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is an
equivalence of categories that preserves and reflects coverings. -/
theorem quasiEtaleSiteEquivalenceStatement : QuasiEtaleSiteEquivalenceStatement.{u, v, z} :=
  quasiEtaleSiteEquivalenceStatement_of openPartitionCoproductStatement.{u, v, z}
    quasiEtaleOpenRestriction.{u, max z v}

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
