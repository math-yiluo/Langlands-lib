# Integral coroot spans on faces of a root datum

Authors: Worker 1577.

This internal algebraic construction concerns a finite reduced root datum over
`ℤ`. It does not assert existence of group schemes or of their root data.
For any integral linear functional on the root lattice, the coroots whose
corresponding roots have zero value span the integral span of a subset of a
suitable simple-coroot base. The ambient character and cocharacter lattices
need not be spanned by their roots and coroots.

The proof uses the published integral base construction in
`Langlands.GroupScheme.SplitExistence.IntegralBase`. A regular functional on a
finite family can be perturbed to agree with any prescribed nonzero signs:
multiply the prescribed functional by an integer exceeding all absolute
values of a regular one, then add the regular one. Its positive vectors have
nonnegative value under the prescribed functional. Applying the integral base
construction gives a simple-coroot base on which the prescribed functional is
nonnegative.

Every coroot is a nonnegative integral combination of the simple coroots or
the negative of one. An induction on additive monoid closure shows that a
combination with value zero uses only zero-valued simple coroots. This proves
the equality of integral spans, with no passage to a rational vector space.
For a functional on roots, composition with the canonical copolarization
transfers its zero indices to the coroots: the canonical norm identity says
that twice the transferred value is the original value times the positive
squared norm of the coroot.

The existence interface is `exists_base_coroot_span_root_zero`.
`RootZeroCorootFace P f` packages a base, a subset of its support, and the
proved integral span equality. The noncomputable construction
`rootZeroCorootFace P f` selects such data from the proved existence result.
Its `base`, `support`, `support_subset` and `span_eq` fields give the
corresponding objects and proofs directly.

This is an internal derivation from the actual root-datum axioms and the
already published integral base construction, intended for the separate
geometric comparison of the actual derived subgroup of a split-torus
centralizer. It does not establish that geometric comparison or any
simple-connectedness result.
