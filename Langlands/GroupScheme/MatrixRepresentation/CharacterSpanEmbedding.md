# Closed split-torus embeddings from spanning character spaces

For a field `k : Type u`, an affine group scheme `G` over `Spec k`, and a finite
coordinate type `n : Type`, let `ρ : MatrixRepresentation G n`. If
`ρ.characterSpan = ⊤`, `characterSpanEmbedding ρ hspan` constructs an actual
homomorphism
`G ⟶ (splitTorus.commGroupScheme (Spec k) (ULift.{u} n)).toGrp`.
The morphism is defined without a faithfulness assumption.
`isClosedSubgroup_characterSpanEmbedding` proves that it is a closed immersion
when `ρ` is a closed immersion. The existence form is
`exists_closed_splitTorus_embedding_of_characterSpan`.

The construction works over any field, in every base universe `u`. It assumes
neither source smoothness nor reducedness, connectedness, or algebraic
closedness. Its character equations hold on all affine test algebras, including
nonreduced ones, and the resulting factorization is an equality of actual
group-scheme morphisms. This result does not establish that the full centre of
a reductive group has a closed representation spanned by character vectors;
that structural input remains a separate obligation for the motivating
normal-centre problem.

`exists_characterBasis` takes the union of the character spaces. Its linear
span is the whole coefficient space. A maximal independent subset of this
union gives a basis, which is reindexed by `n` using invariant basis number.
Each chosen basis vector belongs to one character space. This argument also
includes the empty coordinate type.

`basisCoordinateGL` is the invertible matrix taking ordinary vectors to their
coordinates in the chosen basis. Its specified inverse has the basis vectors
as columns. `basisCoordinatePoint` realizes it as an actual rational point of
the general linear group scheme, and `rationalMatrix_basisCoordinatePoint`
checks the matrix convention. The theorem
`conjugate_basisCoordinatePoint_affineMatrix` applies the published
`characterSpace_affine` equation to each column. Thus the conjugate matrix is
the diagonal matrix of the character values over every test algebra.

`universalDiagonalFactorOver` uses the existing diagonal-locus lift at the
universal affine point and the coordinate-scheme isomorphism to obtain a
factorization on the underlying relative schemes. Since the diagonal torus
inclusion is monic, the factor preserves the identity and multiplication,
giving `universalDiagonalFactor`. Its composite with the diagonal inclusion
equals the representation. The factor is a closed immersion whenever the
representation is closed, by the closed-immersion factor theorem.

Finally, `characterSpanEmbedding` chooses the character basis, conjugates by
its coordinate point, and uses that diagonal factor.
`characterSpanEmbedding_comp` records its composite with the diagonal torus
inclusion. Conjugation is a scheme automorphism, so it preserves closedness,
and the preceding factor theorem gives the claimed closed immersion.

This is an internal derived construction. Its inputs are the published
universal character-space and diagonal-torus constructions and Mathlib's basis
selection, basis matrices, and closed-immersion factor results. No additional
literature assertion is being formalized or assumed.
