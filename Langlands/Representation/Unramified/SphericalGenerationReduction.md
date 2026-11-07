# Fixed-line reduction for spherical generation

This internal support module isolates an algebraic reduction used in the proof
of ordered unramified spherical generation. It does not assert that an ordered
principal series has a spherical irreducible head.

For a smooth complex representation with a coatomic lattice of
subrepresentations, assume that its compact-open fixed space embeds linearly
into the scalars and that it has a spherical strong irreducible head. Compact
fixed-vector surjectivity shows that the head quotient is nonzero on the fixed
space. Any nonzero linear map from a space that embeds in the scalars is
injective. Every maximal proper subrepresentation is the kernel of an
irreducible quotient, hence is the kernel of the supplied head quotient by the
strong-head condition. It therefore contains no nonzero fixed vector. Every
proper subrepresentation lies in a maximal one, proving the generation
criterion.

The finite-length corollary obtains coatomicity from the Noetherian
representation module and the order isomorphism between subrepresentations
and submodules. This argument is an elementary internal deduction from the
published strong-head definition and compact fixed-vector surjectivity.

For the actual unramified principal series, `scalarEvaluation` evaluates a fixed
vector at the identity and uses the canonical equivalence from a tensor product
of copies of the scalars to the scalars. Its injectivity follows from the
published `eq_zero_of_eval_one`, which uses the Borel–maximal-compact
decomposition. This fixed-line assertion imposes no order, distinctness, or
unitarity restriction on the inducing tuple. It is the linear-algebra input to
the reduction; the spherical-head construction remains a separate obligation.

Author: Worker 1650.
