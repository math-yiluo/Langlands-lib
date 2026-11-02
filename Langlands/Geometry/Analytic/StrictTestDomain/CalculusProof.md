# Calculus of strict-test domain representations

Author: Worker 135.

This proof derives the four clauses of `CalculusStatement` directly from the
published `Represents` predicate. Its closing theorem is
`Langlands.Analytic.StrictTestDomain.calculus`. The target and imported pairs
are unchanged. All presented algebras and test objects remain in the coefficient
universe, with no extra nonzero, reducedness or nontrivial-valuation assumptions.

`represents_id` proves that the bounded identity represents the whole spectrum:
its pullback is the identity on seminorms, and every test map factors uniquely
through the identity.

`Represents.postcomp_equiv` transports representation along a bounded algebra
equivalence. The induced spectrum homeomorphism is surjective, so composing the
spectrum map leaves its range unchanged. A factor through the original map is
composed with the bounded inverse equivalence. Uniqueness follows by composing
a competing factor with the forward equivalence. Applying this argument to the
inverse equivalence proves `represents_postcomp_equiv_iff`.

`represents_unique_comparison` applies the two universal properties to obtain
bounded maps in both directions. Each composite and the appropriate identity
factor the same structural map. Uniqueness makes the composites identities.
`BoundedAlgEquiv.ofHomInv` packages these inverse maps and their existing bounds.
A competing equivalence has the same forward map by factorization uniqueness;
extensionality then identifies the equivalences themselves.

`represents_comp_inter` assumes that `i` represents `U` and `j` represents the
inverse image of a closed `W` under the spectrum map of `i`. Closedness of the
intersection follows from the two closedness hypotheses. For the exact image,
a point of `U ∩ W` first lifts along the spectrum map of `i`; its membership in
`W` places that lift in the inverse image represented by `j`, so it lifts again.
Conversely every point pulled back along the composite belongs to both subsets.
A test map with image in `U ∩ W` factors through `i`. Its factor has image in the
required inverse image because its composite is the original test map. It then
factors through `j`. Applying uniqueness first for `i`, then for `j`, proves
uniqueness of the composite factor. No spectral injectivity is used.

The helper `Represents.hasImageIn` obtains the image-inclusion condition from
exact image equality. The public helper `comap_comp_apply` verifies
contravariance pointwise on seminorms and is reused by rational restriction. All constructions use actual bounded algebra maps and
the actual spectra, rather than abstract surrogate objects.

These are derived universal-property arguments, not separately quoted results
from the literature. Their provenance is Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), printed/PDF page 8, Definition 2.1.11
(contravariant bounded algebra maps), and page 9, Definition 2.2.1 (closedness,
exact spectrum image and unique factorization). Registered original:
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

The published predicate tests only presented strict affinoids. Berkovich's
source tests all affinoids, even for a strictly affinoid domain; this proof
retains the weaker published scope. Composition is conditional on two supplied
representations and asserts no existence of arbitrary inverse images or
pullbacks. It proves no arbitrary-radius construction, structure sheaf,
analytic atlas or site.
