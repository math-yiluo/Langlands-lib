# Lie coordinates induced by natural vector coordinates

This internal construction starts with a field `k : Type u`, an actual group
scheme `V` over `Spec k`, and multiplicative equivalences `e T` from its points
on every test scheme `T` to the additive group of `Fin d` tuples of global
functions. Naturality is the existing `IsNaturalVectorCoordinates e`. Neither
a torus action nor a choice of weights is assumed.

`vectorAffineCoordinates e A` combines the equivalence on `Spec A` with
`Scheme.ΓSpecIso` to express affine points as tuples in the coefficient algebra
`A` itself. Its inverse applies the inverse global-section identification and
then the inverse of `e`. The inverse laws follow from the two isomorphism laws;
the group law follows from addition of coordinates. The naturality theorem
combines the supplied all-test naturality with the naturality of `ΓSpecIso`,
and applies to every `k`-algebra map.

For a point of the actual dual-number identity kernel, reduction to `A` is the
identity point. Naturality therefore makes the constant term of every
coordinate zero, as proved by `vectorAffineCoordinates_kernel_fst`.
`vectorLiePoint e he x` is the inverse coordinate image of the pure epsilon
tuple with coefficients `x`. Reduction of this point is the identity, so it is
an element of the actual kernel.

Assuming `IsAffineHom V.X.hom`, `vectorLieCoordinates e he A` identifies
`Additive (lieKernel V A)` with `Fin d → A` as an `A`-linear equivalence.
The forward map takes epsilon coefficients and the inverse is
`vectorLiePoint`. The constant-term vanishing and the pure-epsilon formula
prove the two inverse laws. Addition follows from the group law in vector
coordinates. Scalar multiplication follows by applying coordinate naturality
to the dual-number map which scales epsilon. Applying naturality to the
dual-number coefficient map proves compatibility with every algebra map.

`finiteLieCoordinatesOfVector` packages these equivalences and their
naturality into the existing `Lie.FiniteCoordinates V d` structure. It works
in arbitrary universe `u`, including `d = 0`, and imposes no smoothness or
connectedness assumption.

The provenance is internal: the definitions and proofs are derived directly
from natural vector coordinates, the actual dual-number kernel, and the
Library's scalar multiplication and coefficient-change maps. This helper
supplies finite coordinates for a subsequent differential representation.
It does not diagonalize a vector-group action, identify semigroup subgroups,
or prove `SemigroupOrderedProductStatement`.
