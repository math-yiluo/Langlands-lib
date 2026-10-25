# General linear coordinates as a determinant localization

Author: Worker 57.

For a finite type `n` with decidable equality and a commutative ring `R`, this
module constructs

`determinantLocalizationEquiv n R : CoordinateRing n R ≃ₐ[R] DeterminantLocalization n R`.

The source is the existing general linear coordinate algebra: the polynomial
ring in the entries of two matrices, modulo the equations that they are mutual
inverses. The target is the polynomial ring in the entries of one matrix,
localized at its determinant. The equivalence preserves the original matrix
entries and sends inverse-entry variables to the entries of the inverse of the
localized matrix.

## Internal provenance and scope

This is an internal derivation from the published `GeneralLinear` coordinate
quotient, its universal invertible matrix and classifying-map equivalence, and
Mathlib's matrix determinant and localization APIs. It supplies the explicit
comparison with the determinant localization that the earlier module left open.
It does not introduce another independently chosen model of the group.

The index type is small (`n : Type`); the base ring may lie in any universe.
There is no field, positive-rank, nontrivial-ring or reducedness assumption.
In particular, the construction also applies to the empty matrix index type.
This contribution establishes an algebra equivalence with coordinate formulas.
It does not assert smoothness, reductivity, a scheme-level open immersion, Harris
PEL representability or the construction of scheme levels. The comparison is a
prerequisite for later geometric results about the existing group scheme.

## Construction

`MatrixPolynomial n R` is `MvPolynomial (n × n) R`. The matrix
`matrixVariables n R` has entry `X (i, j)`, and `determinantPolynomial n R` is
its determinant. `DeterminantLocalization n R` is Mathlib's actual localization
away from that polynomial, with its inherited `R`-algebra structure.

`localizedMatrix` applies the localization map to each entry of
`matrixVariables`. Its determinant is a unit because ring homomorphisms preserve
determinants and localization inverts the designated element.
`localizedUniversal` turns this matrix into an element of `GL` using the
established inverse-matrix construction for a unit determinant. Its entries are
exactly the localized polynomial variables.

`toDeterminantLocalization` uses the published `classify` map to specialize the
original coordinate quotient at `localizedUniversal`. Conversely,
`matrixPolynomialToCoordinate` evaluates the single-matrix variables at the
entries of the original universal matrix. The determinant goes to a unit because
that matrix is invertible. The universal property of localization therefore
constructs `fromDeterminantLocalization`. Its formula on elements of the original
polynomial ring is proved by the localization lift equation.

## Inverse laws and coordinate formulas

`localizedUniversal_map_from` proves that the reverse algebra map sends the
localized invertible matrix to the original universal invertible matrix. Equality
of their entries proves equality of these units; no separate inverse-entry
calculation is needed. Applying the published `homEquiv` injectivity and
naturality of `point` then proves `from_comp_toDeterminantLocalization`.

For `to_comp_fromDeterminantLocalization`, localization extensionality reduces
the equality to algebra maps out of `MatrixPolynomial`. Polynomial
extensionality reduces that equality to the entry variables, where the two
explicit evaluation formulas agree. `AlgEquiv.ofAlgHom` packages the two maps
and these inverse laws.

`determinantLocalizationEquiv_entry` and
`determinantLocalizationEquiv_inverseEntry` identify both families of original
coordinate generators under the equivalence. The first gives the localized
variable `X (i, j)`; the second gives the corresponding entry of
`(localizedUniversal n R)⁻¹`. These formulas follow directly from the original
classifying-map formulas, so the comparison retains the previously constructed
matrix coordinates.
