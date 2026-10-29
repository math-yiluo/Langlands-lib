# Bounded comparisons between full domain representations

Worker 56 constructs comparisons between the actual quotient algebras in two
full representations of the same affinoid-domain locus. All declarations
belong to `Langlands.Analytic.PresentedAffinoidAlgebra.Domain`.

## Inputs and constructed maps

The coefficient field `K : Type u` is a complete ultrametric normed field.
The valuation may be trivial. The base `A : PresentedAffinoidAlgebra K`
is an actual finite positive-polyradius closed Tate quotient. Every
`U : Domain K A` stores an actual such algebra, a bounded structural
`K`-algebra map from `A`, a subset of its bounded spectrum, and the full
representation property against every presented positive-radius affinoid.

No new existence of domain representations is assumed or proved here.
The input representations carry the published full universal properties;
the published whole-spectrum construction gives a concrete instance.
There are no reducedness, nonzero-quotient or nontrivial-valuation
requirements.

For `h : U.locus = V.locus`, `isoOfLocusEq U V h` constructs an actual
isomorphism in the published domain category. Its forward arrow is
`inclusionOfSubset U V` for the inclusion obtained from `h`, and its
inverse uses the reverse inclusion. Those arrows contain actual bounded
restriction maps. The full representation property in the imported
construction produces the maps and proves their uniqueness. Each
composite equals the corresponding identity because each domain hom type
is a subsingleton.

Conversely, `locus_eq_of_iso` applies the two arrows' proved subset
inclusions and uses antisymmetry. `nonempty_iso_iff_locus_eq` packages
these two directions. It is an equivalence of propositions about these
specified representations, not a definition of their actual arrows by
subset containment.

## Actual bounded algebra equivalences

`boundedEquivOfIso e` takes a domain isomorphism `e : U ≅ V` and
constructs a `BoundedAlgEquiv K U.algebra V.algebra`. Since the domain
category has the space direction, the forward algebra map is
`e.inv.restriction`, while the inverse algebra map is
`e.hom.restriction`. Applying the two categorical inverse equations to
their restriction maps and then evaluating on each element proves the
two elementwise inverse identities. `BoundedAlgEquiv.ofHomInv` retains
the existing positive linear norm bounds in both directions.

The two application lemmas expose these forward and inverse maps. The
two `comp_baseMap` lemmas prove that they commute with the respective
structural maps from `A`; each is the stored equation of the appropriate
domain arrow.

`boundedEquivOfLocusEq U V h` applies this construction to `isoOfLocusEq`.
Its forward and inverse base equations are proved explicitly. It does
not identify the chosen presentations, their norms or their closed
ideals, and it does not assert an isometry.

`boundedHom_eq_of_over_base` proves uniqueness among all bounded algebra
maps `U.algebra → V.algebra` commuting with the structural maps. Each such
map, with its commuting equation, is a domain arrow `V → U`;
subsingletonness of that hom type identifies the maps. In particular,
`boundedHom_eq_boundedEquivOfLocusEq` identifies any competing bounded
map over `A` with the forward map of the constructed equivalence. A
competing map need not be invertible as an input.

## Topological realizations

`algebraHomeomorphOfLocusEq` gives a homeomorphism of the actual quotient
rings with their norm topologies. It uses the already proved bounds of
the algebra equivalence and its inverse, without an open mapping theorem
or an assumption about scalar valuations.

`spectrumHomeomorphOfLocusEq` has direction
`BanachSpectrum U.algebra ≃ₜ BanachSpectrum V.algebra`. The underlying
map pulls seminorms back along the inverse algebra map; the inverse
pulls them back along the forward algebra map. Both are continuous by
the published bounded comap construction. The theorem
`spectrumHomeomorphOfLocusEq_over_base` proves that composing with
`V.spectrumMap` gives `U.spectrumMap`, by evaluating the inverse algebra
map's base equation on every `a : A` and every seminorm `x`.

This compares two representing spectra. It supplies no proof that an
arbitrary representing spectrum maps injectively to its locus or is
homeomorphic to that locus. It also constructs no new rational domain,
intersection, atlas, structure sheaf or site.

## Provenance and related work

These are derived constructions from the published full representation
property, rather than verbatim source statements. The registered original
is V. G. Berkovich, *Non-archimedean analytic spaces* (Trieste lectures,
2009), source ID `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11, printed/PDF p.8, gives the category dual to bounded
affinoid algebra maps. Definition 2.2.1, p.9, gives the full domain
universal property. Testing each of two representations on the other
representing algebra produces the two bounded comparison maps, and
testing their composites against the identity proves their inverse
equations. This is the source-based rationale for the construction.

The existing strict-test calculus of Worker 135 in
`Langlands.Geometry.Analytic.StrictTestDomain.CalculusProof` proves a
related unique-comparison result for strict presentations and strict
tests. The present module uses the published full `Domain` category,
whose tests have arbitrary positive radii, and constructs categorical
and topological comparisons from its actual restriction maps. It does
not apply the strict-test theorem as a full-domain theorem.
