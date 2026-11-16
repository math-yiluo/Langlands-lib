import Langlands.AlgebraicGeometry.Picard.NormalModelTwoAxisExtensionReduction
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassRepresentabilityReduction
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreReduction
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterion
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassSmallValuesProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassZariskiSheafProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassFaithfullyFlatSheafProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassFilteredColimitsProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassAdicLimitsProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassArtinianLiftingProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassNilpotentInjectiveProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassValuativeSeparationProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassOneDimensionalLiftingProof
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassGenericNonLiftingProof

/-! # Extension of generic two-axis-trivial bundles over normal finite-type integer domains

Proof of `Langlands.AbelianScheme.NormalFiniteTypeTwoAxisExtensionProperty`. Murre's criterion
and the ten Murre conditions for the two-axis class presheaf give its representability over
noetherian affine bases (Raynaud, LNM 119, Theorem III 4.4). The published reduction
`normalFiniteTypeTwoAxisExtensionProperty_of_twoAxisClassRepresentability` turns this
representability into the extension property. -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Every generic line bundle on the self-product of an abelian scheme over an integrally
closed domain of finite type over `ℤ` that is trivial on both unit axes extends to an actual
line bundle on the total self-product. -/
theorem normalFiniteTypeTwoAxisExtensionProperty :
    NormalFiniteTypeTwoAxisExtensionProperty.{u} :=
  normalFiniteTypeTwoAxisExtensionProperty_of_twoAxisClassRepresentability
    (noetherianTwoAxisClassRepresentability_of_murre
      Langlands.AlgebraicGeometry.UnramifiedFunctor.murreCriterion.{u, u + 1}
      noetherianTwoAxisClassSmallValues noetherianTwoAxisClassZariskiSheaf
      noetherianTwoAxisClassFaithfullyFlatSheaf noetherianTwoAxisClassFilteredColimits
      noetherianTwoAxisClassAdicLimits noetherianTwoAxisClassArtinianLifting
      noetherianTwoAxisClassNilpotentInjective noetherianTwoAxisClassValuativeSeparation
      noetherianTwoAxisClassOneDimensionalLifting noetherianTwoAxisClassGenericNonLifting)

end Langlands.AbelianScheme
