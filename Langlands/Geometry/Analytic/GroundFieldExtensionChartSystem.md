# The quotient chart system for extension of the ground field

`IndexedAffinoidAtlas.GroundFieldExtension.chartSystem K L a` keeps the
indices and containments of `a`. Its algebras are `chartAlgebra`, the
ground field extensions of the original presented algebras, and its
`restriction` maps are the extensions of the original bounded restrictions.
Scalar extension preserves their identity and composition equations.

`restriction_represents` applies
`PresentedAffinoidAlgebra.GroundFieldExtension.domainPreservation` to
identify the domain of each extended restriction with the inverse image
of the original domain under the spectrum projection. If a point of an
extended chart lies in two such domains, the projected point lies in both
original domains. The original net supplies a common subchart containing
that projected point, and `mem_range_restriction_iff` lifts the point into
the extended common subchart. This gives the common-subchart axiom of
`AffinoidChartSystem`.

`chartSystem.Space` is the quotient of the disjoint union of the extended
spectra by the common-subchart relation, with the quotient topology.
The spectrum projections followed by the original chart embeddings agree
along the restrictions by naturality. They descend to `projection`,
which is continuous by the quotient topology and satisfies
`projection_chart`. For `range_chart`, if a quotient point projects into
an original chart, take a representative and choose an original common
subchart at the projected point. Lifting the representative into that
subchart gives a representative in the requested extended chart. Thus
the extended chart range is exactly the projection preimage of the
original range. `atlasProjection` packages these laws for the topology
theorem used in `GroundFieldExtensionAtlas`.

The coefficient fields are arbitrary complete ultrametric normed fields
with `NormedAlgebra K L`, in independent universes. The construction
allows arbitrary extension degree, transcendence degree, trivial
valuations, positive radii, nonreduced and zero algebras, empty spectra
and empty atlases.

The chartwise construction is derived from Berkovich, *Étale cohomology
for non-Archimedean analytic spaces* (1993), §1.4, printed p. 30
(PDF p. 27), and the indexed atlas conventions of Definition 1.2.3 and
Remark 1.2.4, printed p. 16 (PDF p. 13). The common-subchart quotient and
its projection package are the Library's implementation of the gluing.
The registered source is `berkovich-1993-etale-cohomology`.
