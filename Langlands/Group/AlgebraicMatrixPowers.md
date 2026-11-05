# Positive diagonal powers inside polynomially defined matrix subgroups

Author: Worker 1571.

This auxiliary construction implements the polynomial part of Borel's
section 6.3, printed pages 42–43, for a matrix subgroup whose membership is
explicitly given by polynomial equations. The source is registered as
`borel-lie-groups-linear-algebraic-groups-2000`, SHA256
`784f2fc696cc43c5e4375b8d1414439cce180a7273caa620aa27a9c4d8d1809c`.
The current Library contains no errata note for that source. The implemented
finite interpolation argument is in `PositivePowerPolynomial`.

For positive real numbers `x i`, `diagonalPower x hx r` is the invertible
diagonal matrix with entries `ofReal ((x i)^r)`. Its inverse has the reciprocal
entries. `conjugatedPower U x hx r` conjugates this diagonal matrix by an
arbitrary matrix unit `U`. At a natural exponent `m`, this is the ordinary
`m`th power of the same family at exponent one.

`doubledValues x` lists both `x i` and `(x i)⁻¹`, all of which are positive.
`conjugatedCoordinate U` gives, for each existing general-linear coordinate,
a polynomial in these doubled variables. The entry coordinate is
`∑ k, (U i k * U⁻¹ k j) * X (inl k)`; the inverse-entry coordinate uses
`inr k`. Evaluating these polynomials at the coordinatewise real power point
gives exactly the entries and inverse entries of `conjugatedPower`. Both kinds
of coordinate are needed to describe closed subgroups of `GL` by polynomial
equations in an affine space.

`IsPolynomiallyDefined H` means that there is a set of polynomials in the
Library's actual `GeneralLinear.Coordinate n` variables such that a matrix
unit belongs to `H` if and only if every polynomial vanishes at its entry and
inverse-entry values. This is an explicit algebraicity assumption in the
auxiliary theorem. It is not a topological closedness assumption.

`conjugatedPower_mem` assumes this property and membership at exponent one.
Subgroup closure gives membership at every natural exponent. Substitute
`conjugatedCoordinate U` into each defining polynomial. Its vanishing at
natural exponents, followed by `eval_powerPoint_eq_zero`, gives vanishing at
every real exponent. Undoing substitution and applying the membership
characterization proves that the whole conjugated positive family lies in
`H`.

The scalar field is any `RCLike` field at universe `u`. The finite matrix
index type `n : Type` may be empty. The theorem does not construct a
diagonalization, prove that an actual scheme-point image has the supplied
polynomial description, or construct a self-adjoint realization of a
reductive group. These and the parabolic covering remain obligations of the
enclosing Iwasawa task.
