# Recovered fixed building pairs with both exact fixer formulas

This internal result constructs compatible full and neutral integral models of
an arbitrary pair of coefficient-fixed points in the supplied reduced building
over the maximal unramified extension. It retains both exact formulas: the
upstairs full integral points are the character-valuation kernel intersected
with the pointwise pair fixer, and the upstairs neutral integral points are the
supplied zero subgroup intersected with that same pair fixer.

`HasRecoveredFixedBuildingPairZeroModels` records this existence using the
published `RecoveredBuildingFixerModels` package and the additional neutral
identity. The construction assumes a connected reductive group over a
nonarchimedean local field, the actual descended torus and its maximal split
base change, the supplied apartment, centralizer and full omega compatibility,
coefficient stability, and fixedness of both endpoints. It works in arbitrary
universe and both characteristics. It makes no claim that full point fixers
are constant along a facet.

The proof first applies the published `MaximalUnramified.commonApartments`
from `IntegerValuationCommonApartmentsProof` to place both endpoints in one
translated apartment. The two apartment coordinates form a nonempty finite
set, so every affine functional has bounded image. The published
`unramifiedParahoricModel` from `UnramifiedParahoricModelProof` supplies an
actual relative component model with both exact formulas on that translated
pair. The image is literally the original pair, including when its endpoints
coincide. Finally, `exists_recovery_of_fixedBuildingSubset` from
`UnramifiedFixedBuildingPairRecovery` descends the full model and its actual
neutral component, using the individual coefficient fixedness of the two
endpoints. The additional neutral identity remains a property of that very
same upstairs model. These are compositions of published inputs, with no new
independent assertion attributed to the literature.
