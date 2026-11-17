# Global Whittaker majorization by an adelic simple-root gauge

The theorem `whittakerSimpleRootMajorization` proves the unchanged published
`WhittakerSimpleRootMajorizationStatement` in every universe. It applies to every
number field with compact additive adelic quotient, every rank, every
`WhittakerDecayClass`, and every common determinant-power bound on its vectors.
The external determinant exponent is the given real number `β`. The simple-root
gauge exponent is zero, uniformly over vectors and standard additive characters.
The Schwartz–Bruhat function and gauge may depend on the vector and character.

The implemented proof first transports compactness of the standard compact
matrix subgroup to the actual adelic group-scheme points. The compact-uniform
diagonal theorem `exists_simpleRoot_schwartzBruhat_bound` supplies a
Schwartz–Bruhat function in the adjacent diagonal ratios and its coordinate
symmetries. That theorem combines archimedean rapid decay, finite-denominator
support, and the smooth symmetric majorant construction explained in its
supporting module pairs.

The symmetries allow `exists_actual_simpleRoot_gauge` to descend the root
function continuously through upper-triangular-times-compact multiplication.
Its extended norm is a measurable gauge on the actual group, invariant under
the full left adelic unipotent subgroup and the right standard compact subgroup.
Applying its triangular-compact formula to a diagonal and the identity compact
element gives precisely the original Schwartz function on the torus.

Finally, `whittaker_le_of_simpleRoot_diagonal_bound` factors every actual adelic
point into a unipotent, diagonal, and standard compact factor. Whittaker
equivariance has unit norm for a standard character, and the determinant norm
is unchanged by the unipotent factor. Gauge invariance and the compact-uniform
diagonal estimate therefore give the required inequality everywhere.

This is an internal combination of the named imported results. The supporting
Markdown pairs explain the constructions and their provenance. The conclusion
is a pointwise majorization result; it does not assert Mellin convergence or
integration on a Whittaker quotient.
