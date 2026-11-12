# Topological assembly of actual geometric Weil reciprocity

Authors: Worker 201 and Worker 95.

This helper derives a reciprocity candidate from two matching range
statements. It is an internal topological construction using the published
actual Weil group, its closed-commutator abelianization, the supplied topology
on field units, and the actual absolute-Galois abelianization. Its conditional
assembly theorem does not assert those range statements without proof;
the companion `WeilReciprocityExistenceProof` module discharges them.

For a continuous injective homomorphism \(f:G\to H\), with \(H\) Hausdorff,
and a continuous homomorphism \(d:G\to D\) into a discrete group, compactness
of the degree kernel makes the map \((f,d)\) inducing. The proof restricts
\(f\) to the compact kernel, where it is a closed embedding. A neighborhood
there is pulled back from \(H\), and its product with the singleton identity
in \(D\) gives the required neighborhood in the product. The reverse filter
inclusion is continuity. The helper also proves continuity of a homomorphism
to a discrete group when its kernel is open.

The supplied normalized order on field units has open compact kernel:
the kernel is exactly the valuation-unit subgroup, which is the zeroth unit
filtration subgroup. The descended Weil degree has compact kernel because
it is the image of actual compact Weil inertia under the quotient projection.

Pair the Weil-to-Galois map with Weil degree, and pair a supplied injective
continuous reciprocity map with normalized order. The published
`toGroupAbelianization_injective` makes the first pairing injective, and
injectivity of the supplied reciprocity map makes the second pairing injective.
The two assumed range inclusions identify their range subgroups.
The resulting group equivalence to field units is continuous in both
directions by the inducing property just proved. Its two product-coordinate
identities give geometric order and equality of its induced Galois map with
the supplied map.

Finally, `weilReciprocityExistenceUniqueness_of_range` obtains the normalized
profinite reciprocity map from the published existence theorem and its
injectivity from the published completion theorem. The candidate construction
and the two range inclusions provide existence with the full geometric
profinite relation. The published `geometricWeilReciprocityUniqueness`
proves uniqueness. The only remaining premises of this helper theorem are the
range statements, which are proved in the companion module for every prime,
carrier universe, field and supplied topological datum.
