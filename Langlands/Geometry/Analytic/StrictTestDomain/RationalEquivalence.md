# Rational sites and presheaves under bounded algebra equivalences

Author: Worker 36.

This derived construction works over a complete ultrametric normed field K.
Its inputs P and Q are actual presented strict affinoid algebras, and e is an
actual K-algebra equivalence with bounded forward and inverse maps. No site
or presheaf isomorphism is assumed as input.

`rationalCategoryEquivalence e` identifies the categories of chosen unit-radius
rational presentations over P and Q. Its forward and inverse functors are the
published rational pullback functors for e and its bounded inverse. The
identity and composition laws for pullback, together with the two inverse
algebra identities, give the unit and counit. The triangle identity follows
from uniqueness of locus-inclusion arrows. Objects retain their chosen data;
this construction does not quotient all presentations with the same locus.

`familyCovers_pullback_equiv_iff` proves that transport preserves and reflects
point-covering families. Preservation is the existing inverse-image argument.
For reflection, lift each spectrum point along the homeomorphism induced by
e, and apply the transported covering property there. No finiteness or
nonemptiness assumption on the index type is used. In particular this
includes the empty family and empty loci. The displayed continuity instances
use the published continuity of rational base change in both directions for
the finite rational Grothendieck topologies.

For a rational input d, `comparisonInverse d e` constructs a bounded map from
the pulled-back quotient to the original quotient by the published extension
construction. Its two input maps are the identity on d's algebra and the
composite of e's inverse with d's structural map. The inverse algebra identity
proves their compatibility. The extension's comparison equation gives one
inverse identity. For the other, uniqueness of bounded maps out of the
pulled-back rational quotient reduces the claim to its base map; the
extension and comparison base-map equations then give the forward inverse
identity of e. `comparisonIso d e` packages these maps as an actual bounded
algebra isomorphism.

`rationalBoundedPresheafIso e` packages the quotient isomorphisms into a natural
isomorphism between the bounded algebra presheaf over P and the presheaf over
Q precomposed with the opposite pullback functor. Naturality is the published
commutation of restrictions and comparison maps. `rationalPresheafIso e`
forgets the norms to give the corresponding commutative K-algebra presheaf
isomorphism. Its forward natural transformation is exactly
`rationalPresheafComparison e.toBoundedAlgHom`, as the final theorem states.

This is internal categorical infrastructure derived from the already proved
rational pullback and extension constructions. Its geometric provenance is
Berkovich, *Non-archimedean analytic spaces*, Trieste lectures (2009),
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p. 9: the rational quotient
construction and the unique factorization characterization are invariant
under bounded changes of the base algebra. The registered source is
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The category equivalence, continuity and natural isomorphisms here are derived
packaging, not separately numbered assertions in that source.

All rational radii remain one, and representation is still tested on presented
strict affinoids. Zero and nonreduced quotients and trivial scalar valuations
are allowed. The presheaf isomorphisms do not prove the rational presheaf is a
sheaf. No full analytic G-topology, general affinoid-domain comparison, atlas,
etale site, or equivariant site is constructed in this module.
