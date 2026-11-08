# Exhausting covariant coordinates by a fixed matrix-coefficient row

This is a derived adapter for the existing matrix-coefficient and actual finite
regular-representation interfaces. It uses `EigenMatrixCoefficient`,
`CovariantRegularFixedLine` through `CovariantSocleIrreducible`,
`MatrixRepresentation.RationalIrreducibility`, and finite-dimensional linear
algebra. No external existence or irreducibility theorem is introduced.

Let `k` be a field in an arbitrary universe, `G` an affine group scheme over
`Spec k`, and `rho` a matrix representation with a finite coordinate index.
Fix a covector `xi`. The coordinate in this module is always the existing
`matrixCoefficient G rho xi v`, with value `xi(rho(g)v)` on every relative
scheme test.

`matrixCoefficientLinearMap` packages its linear dependence on `v`. The proof
checks linearity at the universal point, using matrix-vector and dot-product
linearity. `pointAlgebraHom_matrixCoefficient_rationalRepresentation` identifies
source action by a rational point with right multiplication by its constant
point on every relative test scheme. This follows from the original matrix
multiplication law and naturality of matrix-vector multiplication under the
structure ring map. It imposes no reducedness assumption on the test scheme.

The kernel is consequently a subrepresentation of the original rational-point
representation. A nonzero row gives a nonzero coefficient map: evaluation at
the identity on the standard coordinate vectors recovers each row entry, and
the spectrum global-section isomorphism cancels the scalar map. Rational-point
irreducibility then makes the kernel zero, proving injectivity.

For an affine group morphism `i : H -> G` and any coordinate `chi` of `H`,
supply the eigen-row identity

`xi_T * rho(i(h)) = chi(h) * xi_T`

for every relative scheme `T` and every `h` in `H(T)`. Here the row and scalar
are transported through the original structure maps. The coordinate `chi`
need not be assumed to be a character. The existing all-test covariance
theorem puts every coefficient in the full `leftCovariantSubspace i chi`.
`covariantCoefficientLinearMap` is the corresponding codomain restriction;
it retains injectivity from a nonzero row and rational irreducibility.

`covariantCoefficientLinearMap_bijective` assumes the full covariant space is
finite over `k`, and takes independent dimension bounds

`D <= finrank k (n -> k)` and `finrank k (leftCovariantSubspace i chi) <= D`.

Injectivity gives the reverse dimension inequality. The two spaces therefore
have equal dimensions, so the restricted coefficient map is surjective as well.
`exists_matrixCoefficient_of_finrank_bounds` expresses exhaustion for every
original coordinate satisfying covariance. The upper bound is on the entire
covariant space, not a previously selected regular subspace or socle.

The second translation lemma applies to any finite regular subspace and its
actual regular representation: acting by a rational point corresponds to
right translation on every relative scheme. Its proof specializes the existing
all-test regular-coordinate multiplication formula at a constant point, then
uses the actual matrix naturality formula.

For any basis `b : Basis (Fin d) k (leftCovariantSubspace i chi)`,
`covariantCoefficientBasisMap` expresses the original coefficients in that
basis. Its composite with `affineRegularCoordinateMap` is the original
coefficient coordinate. The two translation formulas, checked at the universal
point, show that this map intertwines the original rational-point action with
the rational-point action of the actual regular representation. The dimension
bounds make it bijective; finiteness of the full space now follows from the
supplied finite basis.

`affineRegularRepresentation_rationalRepresentation_isIrreducible_of_coefficient_bounds`
transfers rational irreducibility using this bijection. The inverse image of
any target subrepresentation is a source subrepresentation, hence zero or the
whole source. Surjectivity transfers that dichotomy to the target. Injectivity
transfers nontriviality. Finally,
`affineRegularRepresentation_isIrreducible_of_coefficient_bounds` uses the
existing implication from rational-point irreducibility to stability-based
irreducibility on all affine tests. Neither transfer requires algebraic
closedness or a reducedness hypothesis on `G`.

All representation, row, eigen-row, finiteness and dimension hypotheses are
supplied inputs. This module does not construct a highest-weight module or a
lowest eigen-row, prove a whole-space upper dimension bound, or assert that
the generic inputs exist for every simply connected group. Those remain
separate obligations in `SteinbergBigCellStatement`; the host proposition is
not proved here.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
