# Dynamic identity-limit embeddings into unitriangular groups

This internal construction works with the actual general linear group schemes and
their points on every test scheme. Reindexing both matrix indices gives a natural
multiplicative equivalence, hence an isomorphism of the representing group schemes.
The point formula is proved through the published global-section comparison.

The existing antitone enumeration of a finite weight vector arranges its weights
in decreasing order. If a matrix satisfies the block identity-limit equations,
the reindexed matrix has diagonal one and all entries below the diagonal zero.
These are precisely the block-unipotent equations for negative index weights.
This includes empty index sets and arbitrary commutative coefficient rings.

For a supplied matrix representation carrying the cocharacter to diagonal form,
the all-test functoriality theorem gives containment in the block identity-limit
subgroup. The sorted containment then lifts through the existing closed
unitriangular representative using `factorHom`. Its composition equation is the
existing factorization equation. If both the original identity-limit inclusion
and the matrix representation are closed, their composite with reindexing is
closed; cancellation through the closed unitriangular inclusion proves closedness
of the constructed factor.

Over an arbitrary field, `exists_closed_unitriangularEmbedding` proves that every
closed representative of the dynamic identity-limit subgroup of an affine group
locally of finite type admits a closed embedding into some standard upper
unitriangular group scheme. The proof takes the published faithful closed matrix
representation from `affineLinearEmbeddingStatement`, conjugates the composite
cocharacter into diagonal form using
`exists_matrix_innerIso_comp_eq_diagonalCocharacter`, and applies the constructed
factor. Conjugation preserves closedness of the matrix representation. The target
dimension is the cardinality of its finite index set; no positive-rank assumption
is used.

This is an internal deduction from the published matrix representation,
cocharacter diagonalization, all-test dynamic functoriality, block-unipotent
representability, and closed-immersion composition and cancellation theorems.
No additional structural result from external literature is asserted. The result
is an embedding construction used toward the dynamic radical theorem;
representation-theoretic unipotence of unitriangular groups and its inheritance
by closed subgroups remain separate inputs. This unit does not establish the
geometric radical or the semistandard intersection theorem.
