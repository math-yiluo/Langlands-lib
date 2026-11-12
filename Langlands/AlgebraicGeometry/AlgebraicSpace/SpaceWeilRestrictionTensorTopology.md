# Tensor Weil comparison with the original factor topologies

This internal supporting unit constructs the local tensor Weil
homeomorphism for actual algebraic spaces, with the original lower
and upper coefficient maps. It retains representability and geometric
hypotheses explicitly and proves neither general representability nor
the adelic endpoint.

For a commutative ring `B`, a topological field `K` with a `B`-algebra
structure, and an algebraic space `X` over `B`,
`fieldBaseChangePointHomeomorph` identifies `X(K)` with the rational
points of its base change to `K`. The source has the field-valued
topology along the identity map of `K` as a `B`-algebra; the target
has the etale-chart topology. Its underlying equivalence is exactly
the inverse of `baseChangeRingPointsEquiv`, since coefficient change
along the identity acts identically.

For a family of commutative `B`-algebras `D i`,
`factorBaseChangeIso` identifies the factor of `X` after base change
to the product with its base change to that factor. The construction
uses `BaseChangeComparison.compIso` and the equality between the
composite spectrum projection and the original `B`-structure map.
`factorBaseChangeIso_points` proves that pulling a product rational
point back along `factorBaseTestMap`, applying this isomorphism, and
returning to `X(D i)` is coefficient change along `Pi.evalAlgHom`.
The proof composes the actual contravariant pullbacks and compares
the underlying test morphisms. When every factor is a topological
field, `factorPointHomeomorph` composes this space isomorphism on
rational points with the inverse field base-change homeomorphism.

The tensor comparison has commutative coefficient rings `R` and `B`,
a nontrivially normed field `C` over `R`, and a finite family of
nontrivially normed fields `D i`. Each factor is a finite-dimensional
`C`-algebra with continuous scalar multiplication and its module topology,
and has its specified
`B`-algebra structure. The given `C`-algebra equivalence
`C tensor_R B` with the product of the `D i` must send `1 tensor b`
to the original image of `b` in every factor. No separability
hypothesis is imposed.

For an algebraic space `X` over `B`, `tensorPointHomeomorph` assumes
algebraicity of its Weil restriction over `R` and of the factor Weil
restrictions over `C`. It also assumes henselian valued-field
conditions on `C` and the factors, and the
`IsQuasiSeparatedLocallyFiniteType` conditions on the factor spaces,
the product Weil space over `C`, and the factor Weil spaces. The
algebraicity witness for the product Weil space is obtained from the
original Weil restriction by tensor cartesian base change.

The homeomorphism has source `X`'s `R`-Weil restriction evaluated at
`C`, with its original field-valued point topology, and target the
product of `X(D i)`, each with its original field-valued point
topology. It composes field base change, the cartesian tensor space
isomorphism, `finiteProductWeilRestrictionPointHomeomorph`, and the
factor homeomorphisms above.

`tensorPointHomeomorph_apply` identifies every forward component
exactly with `completedTensorSpaceWeilRestrictionPointMap`. Its proof
uses finite-product base-point compatibility, the factor base-change
point identity, the cartesian tensor point diagram, and cancellation
of the lower base-change equivalence. Consequently
`isHomeomorph_completedTensorSpaceWeilRestrictionPointMap` proves
that this original map is a homeomorphism for the stated topologies.

The provenance is internal composition of the published field-valued,
cartesian base-change, finite-product, and tensor point comparisons.
All representability and geometry inputs are retained as premises;
none is inferred from the desired adelic conclusion.

The scalar-action premise is `Algebra C (D i)` together with
`ContinuousSMul C (D i)`, generalized from `NormedAlgebra` by Worker 113.
The local Weil comparison needs continuity of the original algebra map
and the module topology, so no equality between the independently
specified field norms is imposed. The same proof and all point formulas
are retained. This permits the standard independently normalized norms
on ramified completions without changing their original topologies.
