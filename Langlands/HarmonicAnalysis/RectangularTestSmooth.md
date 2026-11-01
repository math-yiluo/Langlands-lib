# Uniform open stabilizers of rectangular Schwartz tests

This is an internal topological extension of the published row-test argument in
`RowTestSmoothProof` to the rectangular right action already defined in
`RectangularFourier`. It supplies smoothness needed for the compact-orbit section
construction. No new assertion from external literature is used.

Let `F` be a field with a topology making it a topological ring, and let `r,s`
be arbitrary natural numbers, including zero. A rectangular Schwartz–Bruhat test
is a locally constant compactly supported complex function on the actual space
of `r × s` matrices. Its stabilizer consists of all `g ∈ GL_s(F)` such that
`Φ(Mg)=Φ(M)` for every matrix `M`. Matrix multiplication and inversion show
that this is a subgroup.

The equality `Φ(Mg)=Φ(M)` defines an open subset of `GL_s(F)` times the matrix
space, because both evaluations are locally constant. It contains the identity
times the compact topological support of `Φ`. The generalized tube lemma gives
a neighborhood of the identity on which all points of that support satisfy the
equality. Intersecting this neighborhood with its inverse also controls points
outside the support: if a translate enters the support, the equality for the
inverse translate proves the required equality. Otherwise both values vanish.
Thus the whole stabilizer is open.

This single open subgroup fixes the entire test. Consequently the existing
rectangular Schwartz right-translation representation is smooth. The result
does not need a Hausdorff, local-field, measure, rank or full-support hypothesis.
