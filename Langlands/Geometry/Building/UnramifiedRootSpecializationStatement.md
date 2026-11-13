# Structural root specialization sufficient for unramified root-jump descent

This is an internal geometric prerequisite and a proved conditional reduction.
The existence assertion `UnramifiedRootSpecializationStatement` is unproved.
The module does not prove `UnramifiedRootJumpDescentStatement` without that
prerequisite. Its provenance is an internal decomposition of the published
root-jump target into actual integral-model geometry and the published
supplied-model lifting argument.

The field, connected reductive group, maximal split torus `S`, torus `T`,
factorization, upper maximal split torus, opposite-factor data, upper
apartment data and Omega compatibility are exactly those of the published
root-jump statement. They retain arbitrary universes and both
characteristics. The predicates `fixed`, the restricted root family `φ`,
and the real-cocharacter maps `P` and `Q` have the same definitions as in
that statement. Henselianity of the original integer ring is supplied by
the proved `henselianLocalRing_integer`; it is not an additional hypothesis.

At each Galois-fixed upper apartment point `x`, the new existence statement
requires one actual downstairs relative-component model over `𝒪[F]`, an
integral split torus with generic fibre the original `S`, and actual
special-fibre quotient data. The integral torus inclusion must be closed,
its special fibre maximal split in the neutral special fibre, the quotient
the actual reductive quotient, and the same torus maximal split in that
quotient. The model and quotient are shared by all roots at this point.

For each upper ordinary affine root vanishing at `x` with nonzero pullback
of its derivative, the statement requires an actual lower root `a` and
`IntegralRootSpecializationData` for that lower root in this same model.
The integral generic root sections must have nonnegative value under
`φ x a`, and strictly positive values must reduce to the identity in the
specified residue root quotient. These are precisely
`RootModelReductionCompatible`. It also requires a nonzero real scalar
`c` such that the lower root form on the original real cocharacter space
equals `c` times the pulled-back upper derivative. Thus proportional lower
roots are permitted. It assumes no lower apartment, lower specialness,
carrier identification, rational value-zero witness, or final building
descent result.

The supporting `IntegralRootSpecializationData.exists_zero_rootPoint`
theorem applies the actual quotient-root lifting theorem to the supplied
data. Reductivity of the actual ambient quotient supplies smoothness; base
change of the integral split torus supplies residue splitting. Generic
root representation, model smoothness, residue root representation, and
the smooth closed split-unipotent fppf kernel are retained fields of the
data. Henselian reduction and split-unipotent torsor lifting then produce
an actual generic root point with value exactly zero. The stronger
`RepresentsIntegralRoot` predicate is not used or asserted.

`unramifiedRootJumpDescent_of_rootSpecialization` proves the implication
from this geometric existence statement to the exact published
`UnramifiedRootJumpDescentStatement`. It selects the common model and the
root package, invokes the supporting zero-point theorem, and uses
`LinearMap.ker_smul` for the nonzero scalar to obtain the required equality
of derivative kernels. The structural existence statement remains the
substantive unproved obligation, including construction of the generic
root models and comparison with the specified upper affine roots.
