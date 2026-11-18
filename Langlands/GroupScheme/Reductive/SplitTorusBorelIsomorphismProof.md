# Isomorphisms and conjugacy over a connected Picard-trivial base

Worker 686, with Worker 591 supplying the global pinned descent and affine
conjugacy constructions.

`Langlands.GroupScheme.reductiveSplitTorusBorelIsomorphism` has exactly the type
`ReductiveSplitTorusBorelIsomorphismStatement.{u}` for every universe `u`.
It proves both clauses of the unchanged statement: isomorphisms preserving the
specified split maximal tori, and simultaneously any supplied containing Borel
subgroups, over a connected scheme whose actual line bundles are trivial; and
conjugacy by actual points of `G(S)` when the base is affine.

The proof first installs the given connectedness instance. For each of the two
reductive groups, `exists_globalCoordinateRootDatumOf_of_connected` constructs
a full global coordinate root datum on the original character and cocharacter
lattices. The root-index types are finite by these data; the proof chooses
finite enumerations for them and for the original coordinate tori.

`CoordinateRootDatum.picardRootFrames` applies the given hypothesis
`∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S)` to the actual root-weight
line bundles. It provides linear trivializations of the actual root-weight
modules on every affine test. `picardRootFrames_isCoherent` gives their
compatibility as actual root-vector dual-number points in the original groups.
Thus neither the root data nor the frames are additional hypotheses.

For the first isomorphism,
`CoordinateRootDatum.torusIsoOfEtaleLocalIsoOfCoherentFrames` combines these
data and coherent frames with the given étale-local group isomorphisms and
`affinePinnedIsomorphismTheorem`. It returns an actual group-scheme
isomorphism with the required equality of torus range functors. For arbitrary
supplied relative Borels containing the tori,
`torusBorelIsoOfEtaleLocalIsoOfCoherentFrames` supplies an actual isomorphism
and both range equalities. Its imported construction selects Borel-compatible
bases, compares the full based root data, and descends compatible affine pinned
isomorphisms. The affine pinned theorem is proved by its imported proof module;
it is not a parameter of the theorem here.

For the affine clause the proof installs the supplied `IsAffine S` instance
and applies `connectedPicardAffineSplitTorusBorelConjugacy` with the original
Picard, reductivity, closedness and maximality hypotheses. This gives both the
torus conjugating point and the simultaneous torus/Borel conjugating point in
`G(S)`. Equality of range functors in both clauses is equality on every relative
test scheme, exactly as in the target.

This is an internal composite proof of the statement corresponding to Conrad,
*Reductive group schemes* (2014), Proposition 6.2.11(2). The source correspondence
is documented in the imported statement's Markdown; the implemented proof route
is described above and in the imported construction modules. The statement and
all its imports are unchanged. No pinning, prescribed root datum, root-space
basis, affine hypothesis for the first clause, or extra geometric condition is
assumed.
