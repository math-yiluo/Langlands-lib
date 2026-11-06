# Descending actual rank-one neighbourhoods from etale bases

This internal adapter permits the actual rank-one transporter section to
exist after an affine etale base change. It constructs a good open in the
original affine base and retains the supplied original-fibre root/profile
and local-section inputs explicitly. It does not prove the final general
openness theorem or supply the forward field root/reflection data.

The transporter-coordinate lemma works over any morphism of base schemes.
It starts with an actual point satisfying the all-test transporter relation
for the two actually pulled-back torus homomorphisms. Precomposition with
the inverse canonical split-torus base-change isomorphism expresses those
homomorphisms in the standard torus coordinates of the new base. The
published arbitrary-base-change compatibility of `exponentIso` identifies
the pulled-back integral automorphism with the same integral-coordinate
automorphism on that new base. The point and its all-test transporter
relation are retained exactly.

`rankOneIdentityComponentReductiveNeighbourhood_of_affineEtale` concerns a
smooth affine group scheme over any commutative ring, a supplied closed
standard torus, and a specified base point. The original actual geometric
identity-component torus must be self-centralizing there. Its full actual
root support must be exactly a specified nonzero integral vector and its
negative, and the two actual relative weight ranks must be one. These
ranks equal the corresponding actual geometric weight dimensions. A
specified integral lattice automorphism must invert that vector.

The local inputs are an affine etale base morphism, a point mapping to the
original point, and an actual section of the actual pulled-back group.
The section satisfies the corresponding all-test transporter relation in
canonical standard-torus coordinates. The supplied
`SectionIdentityNeighbourhoodData` places that section inside the actual
geometric identity components on a neighbourhood of the lifted point.

The implementation first proves that the pulled-back torus is closed.
The exact inverse-image equality for the actual geometric self-centralizer
locus gives self-centralization at the lifted point. Exact affine
base-change comparison of the actual root support and weight ranks gives
the same two-root line profile there, using the respective chosen algebraic
closures of the actual residue fields. The existing
`rankOneIdentityComponentReductiveNeighbourhood` then constructs a good open
at that point by the published field theorem `rankOneWeylReductivity`.

Finally, an etale base morphism is open. The image of this good open is an
actual open set of the original base, contains the original point, and
lies in its actual reductive geometric identity-component locus by the
proved actual-group base-change equality for that locus. Transport along
the supplied equality of base points gives the stated neighbourhood type.

The provenance is internal: arbitrary-base-change integral automorphism
compatibility and actual profile comparison, followed by the existing
rank-one construction and open-map descent. The underlying actual
section-in-identity-component construction is by Worker 1683 and is reused
with its exact actual-fibre comparisons. No characteristic, reducedness,
noetherian or connected-ambient-fibre restriction is introduced.
