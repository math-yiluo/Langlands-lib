# Closed-cover atlas incidence and constructible overlap images

This internal construction combines the actual represented atlas kernel pair
with the finite connected closed-cover quotient-component formula. It then
proves constructibility and generic constancy of the overlap image predicates
needed in a geometric spreading argument.

`atlasCoverIncidence a ha s i j` is witnessed by a point of the actual
representing kernel pair of the chart `a`, whose second and first projections
lie in `s i` and `s j`, respectively. The quotient-point equality
characterization from `AtlasComponentIncidence` identifies this relation with
the assertion that some point of `s i` and some point of `s j` have equal chart
images. No closedness or connectedness is needed for this identification.

For a geometrically surjective étale chart and a finite closed cover of its
source by nonempty connected subspaces,
`atlasClosedCoverConnectedComponentsEquiv` identifies the generated incidence
quotient on the cover labels with the actual connected components of `Points F`
using exactly `pointTopology F`. The closed-cover hypothesis belongs to the
scheme chart; its images in the presheaf point space need not be closed.

If the chart morphism to the base is locally of finite type, its overlap is
locally of finite type over the base: its represented projection to the chart
is étale, and composition preserves local finite type. Over a Noetherian base,
quasi-compactness of the chart and quasi-separatedness of the algebraic space
make the overlap Noetherian. The proof uses the published theorem that its
comparison to the chart's self-product is a base change of the quasi-compact
diagonal; the chart self-product is quasi-compact.

`atlasCoverIncidenceLocus a ha s i j` is the image in the base of the intersection
of the inverse images of `s i` and `s j` under the two overlap projections.
For closed `s i`, that intersection is closed in the Noetherian overlap and
therefore constructible. Its finite-type image is constructible by the scheme
image theorem. For finitely many labels, the existing constructible-membership
lemma gives one open neighbourhood of a generic point on which all these
image predicates have the same truth values as at the generic point.

This unit does not identify these base image predicates with the incidence of
the geometric base changes of the cover. That compatibility, geometric
connectedness and covering after spreading, the finite splitting base change,
and arbitrary-ring approximation remain separate inputs to the host theorem.
