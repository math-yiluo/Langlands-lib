# Split root subgroups and their Lie lines

`SplitRootSubgroupStatement` formulates Milne, *Algebraic Groups* (2017),
Definition 21.10 and Theorem 21.11(b)–(c), pp. 428–429 (PDF pp. 444–445),
for the actual root subgroup of a split maximal torus in a connected
reductive group over an arbitrary field. The character must be a root
of the adjoint action on the Lie algebra. In this split setting the
only positive multiple of the root occurring as a weight is the root itself.
Thus the full positive-weight Lie characterization of the intrinsic root
subgroup specializes to Milne's root line.

For each such character `α`, there is a closed group scheme homomorphism
`x` from the one-coordinate additive group `VectorGroup.groupScheme (CommRingCat.of k) 1`
whose image represents `RelativeRoot.subgroup i α` on every scheme test.
Conjugation by a torus point scales the additive coordinate by its value
under `α`. The image of the differential of `x` is the entire weight space
`weightSpace i α`.

For a smooth closed subgroup stable under the torus on all tests, containment
of the root subgroup is equivalent to containment of the root weight space
in its intrinsic tangent image in `Lie G`. This is the containment criterion
of Theorem 21.11(c), which uses Proposition 16.64(a), p. 348 (PDF p. 364).
The tangent image uses the identity kernel on the dual-number test.
The criterion allows disconnected smooth closed subgroups.
