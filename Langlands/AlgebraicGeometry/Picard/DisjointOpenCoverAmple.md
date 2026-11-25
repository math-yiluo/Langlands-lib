# Ampleness assembled over a disjoint open cover

This internal module assembles ampleness from the actual restrictions of
a line bundle to a disjoint open cover. It also supplies the actual
scheme decomposition used in the proof.

For a family `U i` of pairwise disjoint opens covering a scheme `X`,
`disjointOpenCoverIso` identifies the actual coproduct of the open
subschemes with `X`. The comparison morphism is the coproduct
descendant of the actual open inclusions. Its component formula is
`disjointOpenCoverIso_ι`. This construction has no finiteness,
compactness or nonemptiness hypothesis on the cover.

On a compact quasi-separated scheme, the theorem
`LineBundle.isAmple_of_disjoint_openCover` proves ampleness of an
actual line bundle `L` if every actual inclusion pullback
`(LineBundle.pullback (U i).ι).obj L` is ample.

For a finite cover, transport `L` to the actual scheme coproduct
along `disjointOpenCoverIso`. The existing finite-coproduct ampleness
criterion applies; actual module pullback composition identifies its
component restrictions with the prescribed ones. Pullback along the
inverse scheme isomorphism and the actual pullback identity comparison
return ampleness on `X`. Compactness and quasi-separatedness are
transported across the scheme isomorphism.

For an arbitrary disjoint cover, compactness selects a finite subcover.
It is still pairwise disjoint, so the finite result applies. Empty
schemes and empty chosen subcovers are covered by the same proof.
No noetherian assumption is used.

The specialization `FiniteLocalFrames.isAmple_of_rankOpen` applies
this result to the previously constructed disjoint clopen rank loci
of any actual finite frame cover. It assembles ampleness on all
those actual inclusion pullbacks without imposing a global
constant-rank hypothesis.

The provenance is internal: the proof combines the existing scheme
coproduct description for disjoint open subschemes, actual module
pullback comparisons, compact finite-subcover extraction and the
existing finite-coproduct ampleness theorem. It supplies the assembly
step and makes no claim that a particular determinant is positive on
any rank locus.
