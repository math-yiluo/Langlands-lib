import Langlands.Cohomology.Continuous.CorestrictionCompatibilityProof
import Langlands.Cohomology.Continuous.CorestrictionIndexProof
import Langlands.Cohomology.Continuous.CorestrictionTowerProof

universe u

namespace Langlands.Continuous

/-- The index and tower identities on actual continuous cohomology. -/
theorem continuousCorestrictionIndexTower : ContinuousCorestrictionIndexTower.{u} :=
  ⟨continuousCorestrictionIndex, continuousCorestrictionTower⟩

/-- All four continuous corestriction laws, without additional law assumptions. -/
theorem continuousCorestrictionLaws : ContinuousCorestrictionLaws.{u} :=
  ⟨continuousCorestrictionCompatibility, continuousCorestrictionIndexTower⟩

end Langlands.Continuous
