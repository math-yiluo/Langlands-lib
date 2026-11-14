# Surjectivity on zero subgroups

These internal geometric lemmas support the z-extension step of the proof of
Kaletha–Prasad, Proposition 11.5.4 (printed page 431, PDF page 462).
`MapsZeroPointsOnto E EH p` is the reusable property that the image of the
source datum's actual zero subgroup under `p` equals the target datum's zero
subgroup. It imposes no centrality or kernel assumptions. The two final lemmas
prove this property for compatible torus squares and for every central
surjection with torus kernel, respectively. This is an internal definition for
the reduction, rather than a new definition attributed to the book.

The proofs are derived from the published central-surjection, central-cover,
maximal-torus centralizer and split-torus image results.

The simply connected image maps onto the target image because the composite
of the source cover with the derived central isogeny is another semisimple
central isogeny. The universal property of the target simply connected cover
then lifts its points.

In a compatible maximal-torus square, the full central kernel lies in the
self-centralizing source maximal torus. Represented-subgroup factorization
identifies the kernel of the torus restriction with that ambient kernel.
For split tori, the fppf image of the source torus is a maximal split torus
in the target group, hence equals the supplied target torus.

The torus restriction is surjective on integral cocharacters after a common
splitting extension: its base-changed kernel is again a torus, hence smooth
and connected, and the flat surjective split restriction is an epimorphism.
The published smooth-connected-kernel cocharacter theorem applies.

A common finite Galois splitting field is embedded into the prescribed
separably closed extension using an algebra embedding and its field range.
Transport along the resulting algebra isomorphism preserves both split
structures. Independence of the local norm subgroup from its splitting field
then reduces the actual norm-image equality for arbitrary defining data to
the published torus Iwahori surjectivity theorem over this common field.

The zero subgroup is the join of the simply connected image and the image of
the torus norm subgroup. A group homomorphism preserves this join. The two
image equalities therefore give equality of the zero subgroups for compatible
torus squares. For an arbitrary central surjection with torus kernel, the
target is quasi-split over the unramified closure. The maximal-torus square
constructed in `CentralSurjectionZero` supplies a compatible target defining
datum. Independence of the zero subgroup from that datum gives the equality
for every original pair of defining data.
