import Langlands.GroupScheme.RelativeLevi.BorelConjugacyReduction
import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleConjugacyProof

/-! # Borel subgroup schemes are conjugate étale-locally -/

universe u

namespace Langlands.GroupScheme

/-- Borel subgroup schemes of a reductive group scheme are conjugate
étale-locally on an arbitrary base. -/
theorem relativeBorelEtaleLocalConjugacyStatement :
    RelativeBorelEtaleLocalConjugacyStatement.{u} :=
  relativeBorelEtaleLocalConjugacy_of_parabolic
    relativeParabolicEtaleLocalConjugacyStatement

end Langlands.GroupScheme
