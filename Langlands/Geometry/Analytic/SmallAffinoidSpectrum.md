# Small realizations of actual affinoid spectra

This internal construction uses a supplied `Small` instance for an actual
presented affinoid spectrum to place its analytic presentation in an independent
space universe. It transports the existing singleton atlas along
`Shrink.homeomorph`; the original affinoid algebra and bounded restrictions are
retained. Saturation then supplies every local full domain in the same space
universe, which is also the enlarged index universe.

The map construction starts with the original bounded algebra map as its
singleton pullback. Its continuous map is conjugated by the two canonical
spectrum homeomorphisms. Singleton target indices prove coefficient coherence,
so the existing saturation extension constructs all admissible bounded maps.
The identity and composition proofs first compare the complete original bounded
maps, then use functoriality of saturation. Equality on spectrum points alone
is not used to identify algebra maps. The point equation retains exactly the
original spectrum map under the canonical homeomorphisms.

The provenance is internal: this combines the existing singleton spectrum
atlas, transport of atlases along a homeomorphism, Mathlib's small topological
realization, and the constructed compatible saturation functor. It does not
assert étaleness of any map or unrestricted analytic étale pointwise lifting.
