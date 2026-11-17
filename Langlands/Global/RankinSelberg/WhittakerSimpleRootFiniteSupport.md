# Finite-place support in adelic simple-root coordinates

This internal helper applies the Library's finite-level absorption argument
directly to simple roots of finite adelic diagonal matrices. It makes no claim
to construct a gauge or prove convergence.

`diagonal_conj_one_add_simpleRootColumn` extends the normalized column
conjugation identity to the corresponding unipotent matrix. Distribute matrix
multiplication over the identity and the column matrix; the identity term
cancels by invertibility and the column term uses the companion identity.

`exists_conj_simpleRoot_finCol_eq_pow` considers a finite simple-root
translation with parameter `(d_i / d_(i+1)) δ t`, where `t` is integral.
Conjugating by the finite diagonal cancels the root ratio. The result is the
`δ`th power of the integral unipotent with parameter `t`. Its inverse is also
integral because the column matrix is square zero.

`exists_simpleRoot_finite_annihilator` fixes a vector, standard additive
character and compact set of right factors. It finds one positive integer
`δ` such that every nonzero Whittaker value at `a k` forces the character to
be trivial on `(d_i / d_(i+1)) δ Ô` at each finite simple root, whenever the
finite component of `a` is the diagonal `d`.

The finite-level subgroup of the vector is open. The published compact
absorption lemma gives one exponent whose integral unipotent powers lie in
that subgroup after conjugation by every compact right factor. The normalized
translation above therefore fixes the Whittaker value by right invariance.
Its left equivariance multiplies the same value by the character. A nonzero
value forces this factor to be one.

`exists_simpleRoot_finite_denominator` applies the classification of standard
characters and the published finite-adelic dual-denominator lemma to this
annihilator. One nonzero rational coefficient makes every finite simple root
integral. This coefficient may depend on the character, vector and compact
set, but is independent of the diagonal and of the simple-root index.

`exists_simpleRoot_finite_compact_support` contains those roots in the image
of the compact integral finite adeles under multiplication by the inverse of
that rational coefficient. This supplies a common compact support bound for
all the finite simple-root coordinates at nonzero Whittaker values.
