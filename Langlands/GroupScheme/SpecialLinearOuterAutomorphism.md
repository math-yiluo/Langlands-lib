# Centre-moving automorphisms of split special-linear groups

This internal derived module removes the torus-compatibility premise from the
published special-linear automorphism classification. It treats every field,
characteristic and rank and every relative test scheme.

`exists_inner_torusCompatible` applies rational conjugacy of maximal split tori
to the pinned inclusion composed with the automorphism and the original pinned
inclusion. Postcomposing with the resulting rational inner automorphism gives a
commutative square with an actual automorphism of the pinned torus.

`exists_outer_matrix` chooses the published split pinning, arranges that square,
and uses the full-centre nontriviality lemma to select the inverse-transpose
branch of `specialLinearTorusAutomorphism`. Inner automorphisms fix the full
centre, so postcomposition preserves the centre-moving premise. The constant
matrix of the conjugating rational point removes the inner correction. The
resulting formula holds on every test scheme, including nonreduced schemes.

`outerMatrixData` packages a chosen matrix and this proved formula as a
subtype witness, for use by descent constructions.

The provenance is internal composition of the cited Library theorems; this file
does not assert a new literature attribution or a descent result for nonsplit
forms.
