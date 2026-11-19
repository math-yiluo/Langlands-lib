# Ordinary point lifting from localized étale pullbacks

Author: Worker 271.

For strong maps `f : A ⟶ C` and `g : B ⟶ C` with `f` canonically strong étale,
`exists_recognizedLocalizedPullback_point` lifts every pair of ordinary points
with the same image to the particular localized pullback constructed by
`recognizedLocalizedPullback`. The field universe `u` is independent of the
common space and atlas-index universe `v`.

The recognized maps have the original point maps. The proof lifts the pair
into the recognized fibre-product chart system using `FibreProduct.exists_point`.
The published finite Banach pushout proof provides the smallness input for the
recognized product. The shrinking homeomorphism carries the lifted point to
the chosen cone object. Each projection first undoes the shrinking and then
applies the inverse recognition comparison, which acts as the identity on
ordinary points. The two equations therefore give the original points.

`strongEtalePointwiseBaseChange_of_localizedEtalePullback` converts a proof of
`LocalizedEtalePullbackStatement` into the strong pointwise base-change input
of `EtalePointwiseLifting.GeometricInputs`. Refine the supplied localized
pullback to its complete strong square with an étale second projection using
`exists_refinedStrongPullback_of_localized`. Its localized lifting property
maps the recognized cone into the refined square. Functoriality transports the
prescribed point equations, and the refined pullback data give equality of the
full strong composites.

This is an internal construction from the Library's recognized pullback,
point lifting, and refinement APIs. The conditional base-change conversion
retains `LocalizedEtalePullbackStatement` as its geometric premise.
