# Gluing monic subgroup representatives

This derived internal construction gives a monic group-scheme
representative of a Zariski-local actual subgroup functor when such
representatives exist over an open cover of the base. It works over every
scheme in every universe and assumes neither closedness nor reductivity.

`Scheme.ClosedSubschemeGluing.isOpenImmersion_chart_of_mono` generalizes the
existing closed-chart argument to a monic local representative. The chart
uses the existing condition subfunctor, chart map and open-preimage
factorization. The proof constructs its pullback over each test section as
the inverse image of the ambient open. Monicity of the local representative
supplies the cancellation needed for uniqueness.

`Scheme.ClosedSubschemeGluing.exists_mono` uses the published condition
subfunctor's sheaf theorem and locally-surjective chart theorem. Mathlib's
local representability theorem glues the open charts into a scheme.
The image of its identity morphism defines the global map into the ambient
scheme. Naturality identifies composition with that map with the representing
bijection on every test scheme, giving both the factorization criterion and
monicity.

`SubgroupFunctor.exists_isRepresentedBy_of_openCover` applies this construction
to the published absolute membership condition `schemeCondition` of an actual
subgroup functor. The cover of the ambient scheme is the pullback of the base
cover. The given local group inclusions represent the condition on that cover,
using the existing base-change and membership equivalences. Locality on every
test scheme supplies the sheaf condition. The resulting monic scheme map is
regarded as a map of schemes over the base, and the published `representingHom`
construction transfers the group structure to its domain. Its
`isRepresentedBy_representingHom` theorem gives exactly the original subgroup
functor, on arbitrary test schemes. `gluedRepresentative` chooses this group,
inclusion and proof of representation.

The scheme-chart proof generalizes the implemented proof in
`Langlands.AlgebraicGeometry.ClosedSubschemeGluing`; the subgroup
application follows the actual-membership and group-transfer construction in
`Langlands.GroupScheme.SubgroupFunctor.ClosedGluing`.
The present proof reuses their published definitions and generic lemmas and
adds the monic versions. It does not use any theorem asserting global
closedness of relative parabolics and does not construct a parabolic parameter
scheme.
