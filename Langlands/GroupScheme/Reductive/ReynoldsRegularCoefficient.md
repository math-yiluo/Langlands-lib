# Normalized regular maps with diagonalizable-invariant image

Worker 1628. This internal construction combines the published normalized
coefficient map with the diagonalizable Reynolds projection. It retains the
coalgebra chosen by the supplied corepresentation for the actual regular
representations.

`comul_leftAct` proves that left contraction commutes with the right regular
coaction. The proof contracts the second tensor factor by every linear
functional, uses commutation of left and right contractions, and then uses tensor
separation. `coactionCoordinates_mulVec_expand` identifies the vector represented
by a coordinate matrix with its original linear combination.

`reynoldsCoefficientFamily` applies the zero-character projection to a
normalized row of an actual representation's universal coefficient matrix.
The preceding comultiplication identity shows that this projected family
satisfies the same coaction equation as the original row.

`exists_finite_diagonalizable_regular_map_to_one` starts from an actual finite
matrix representation and a nonzero vector fixed on every scheme test. It also
takes a bialgebra map `r` from the corepresenting coordinate bialgebra to
`k[Λ]`. The normalized coefficient family lies in a finite regular span. Its
image under the Reynolds projection is finite dimensional and remains stable
under every right contraction. A finite basis produces an actual regular
representation and an intertwining coordinate matrix.

Every coordinate in that image satisfies `(r ⊗ id) Δ(w) = 1 ⊗ w`.
The supplied fixed vector maps to the constant function `1`: normalization gives
this equation before projection, and the Reynolds projection fixes `1`.
The intertwining equation is proved at the universal affine point, using the
actual regular representation's coaction matrix, then extended to every affine
algebra test by the existing naturality theorem.

The field universe is arbitrary. The abelian character group may have torsion
and need not be finitely generated. No characteristic or centrality restriction
is used. The bialgebra map `r` is supplied; identifying it with restriction along
an actual torus homomorphism requires a separate coordinate comparison. This
construction establishes no Steinberg-module existence, irreducibility,
self-duality or tensor-square exhaustion, and does not prove the final
positive-characteristic conjugation-map proposition.
