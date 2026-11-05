# Base change of the original subgroup multiplication

This internal helper module proves that the actual subgroup multiplication
`subgroupMultiplication j c` commutes with arbitrary change of base, after the
canonical binary-product comparison. The proof expands the original product
of point morphisms and uses preservation of the group operation and of the two
product projections. It imposes no homomorphism condition on multiplication.

`subgroupMultiplicationBaseChangeIso` names this canonical comparison: its
source is the pullback of the product of the two underlying slice objects,
and its target is the product of their pullbacks. It is the standard
`prodComparisonIso` for slice pullback. The multiplication compatibility and
descent lemmas use this isomorphism directly.

The underlying square for every base-changed morphism in the slice category
is cartesian. Smoothness descends through this square along an fpqc base
morphism by Mathlib's descent theorem. Scheme surjectivity descends through
the same square along any surjective base morphism, using surjectivity of the
projection and cancellation of a composite. The final helpers apply these
facts to the original multiplication, including the case of a field extension.
All comparisons are identities of scheme morphisms; no lifting assertion on
all test-point sets is assumed.

The provenance is derived from categorical pullback identities, the existing
actual subgroup multiplication, and Mathlib's descent results. These helpers
support the finite-field split-unipotent product criterion.
