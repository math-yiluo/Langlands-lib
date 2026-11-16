# Matrix conjugation fixes the full centre of the special linear group

This internal prerequisite connects the full centre functor to the published
matrix classification of torus-preserving special-linear automorphisms.

Over every commutative coefficient ring and for every finite matrix index type,
a central determinant-one matrix is fixed by conjugation by any invertible
matrix. The proof uses Mathlib's `SpecialLinearGroup.toGL_mem_center_iff` to view
it as central in the general linear group, then commutes and cancels the
conjugating matrix. Empty and singleton index types are included.

A point of the full scheme-theoretic centre of the actual special linear group
has a central determinant-one matrix over its actual global-section ring. The
proof applies the point equivalence to the defining commutation with all points
over the same test scheme.

`SpecialLinear.HasPointwiseMatrixConjugation f` says that for each test scheme
there is an invertible matrix implementing `f` on every point over that scheme.
The matrix can depend on the test scheme; no compatibility or base-point origin
is assumed. Such an automorphism fixes the full scheme-theoretic centre, by the
two preceding lemmas and injectivity of the matrix point equivalence. This
conclusion tests every scheme and retains nonreduced centres.

For an arbitrary field, let an automorphism of split `SL_(n+1)` preserve the
torus of an actual split pinning, with the specified commuting square. If it
does not fix the full centre, the associated based-root action moves some simple
vertex. The proof is contraposition: if every vertex were fixed, the published
`specialLinearTorusAutomorphism` theorem would give the all-test matrix
conjugation formula, implying centre fixation. The assertion uses the full
root-datum equivalence and based projection of that same compatible
automorphism. It adds no characteristic or universe restriction.

The provenance is internal composition of the cited Mathlib matrix-centre lemma,
the actual centre and point equivalences, and the published special-linear
automorphism theorem. This file does not descend an algebra anti-equivalence or
construct a centre-moving kernel automorphism from a relative Weyl element.
