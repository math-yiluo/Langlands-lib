# Characteristic-polynomial class functions and the hypersurface `f = 0`

This module constructs two kinds of actual class functions from a finite matrix
representation:

- the coefficients of the characteristic polynomial;
- the function `f = det (1 - ρ)`.

It then proves that `f` restricts to zero along Steinberg's substitute product
`N''` for the even type `A` case. In Steinberg's notation (1965, Corollary 9.19)
the function is `f = Σ_i (-1)^i χ_i`, the alternating sum of the fundamental
characters of the `A_{2m}` factor. In the standard representation of `SL_{2m+1}`
this is `det (1 - x)`. Its zero locus `V''` is the stratum on which `N''` is
used. This module works with `det (1 - ρ)` directly. It does not identify `f`
with the alternating sum of fundamental characters.

## Setting

The class functions are in `Langlands.GroupScheme.MatrixRepresentation`. They are
defined for an actual matrix representation `ρ` of an actual affine group scheme `G`
over an arbitrary field `k`. They are elements of the Library's
`ClassFunctions.algebra G`, the actual invariant subalgebra of the coordinate
algebra `ClassFunctions.Coord G`. `Lie.pointCoordinates G g` evaluates a
coordinate at an affine point `g` with coefficients in a commutative
`k`-algebra `A`. The vanishing theorem is in `Langlands.GroupScheme.SplitPinning`.
It uses the setting of `Rational.PathMiddleLine`.

## Definitions

- `charpolyCoeffCoordinate ρ i` is the `i`-th coefficient of the characteristic
  polynomial of the universal matrix `ρ.universalCharacterMatrix`, and
  `charpolyCoeffClassFunction ρ i` is the same coordinate as an element of
  `ClassFunctions.algebra G`.
- `detOneSubCoordinate ρ` is `det (1 - ρ.universalCharacterMatrix)`, and
  `detOneSubClassFunction ρ` is the same coordinate as an element of
  `ClassFunctions.algebra G`.

## Results

- `charpolyCoeffCoordinate_evaluate`: at every affine point `g` over every
  commutative `k`-algebra `A`, the coordinate evaluates to the `i`-th coefficient
  of the characteristic polynomial of the actual matrix `ρ(g)`.
- `detOneSubCoordinate_evaluate`: it evaluates to `det (1 - ρ(g))`.
- `charpolyCoeffCoordinate_mem` and `detOneSubCoordinate_mem`: both are invariant
  under conjugation.
- `restriction_steinbergModifiedProduct_detOneSubClassFunction_eq_zero`: assume
  the hypotheses of
  `PathMiddleLine.det_one_sub_steinbergModifiedPolynomialMatrix_eq_zero_of_path`.
  So `ρ` is a highest-weight representation at the fundamental weight of the end
  of a path component `β`. The merged simple roots of the modified data are
  `β i` and `β (i + 1)`, the complementary representatives are canonical, the
  merged representative is root-generated, and `v` is a nonzero vector of the
  line of `ε_{i+1}`. Then the restriction
  `ClassFunctions.restriction G N''` of `detOneSubClassFunction ρ` is zero, for
  the published modified product `N''`
  (`steinbergModifiedProduct D e x (canonicalSimpleReflectionRepresentatives x)`).
  By the published `ClassFunctions.restriction_spec`, this says the composite
  `N'' ≫ ClassFunctions.rho G` lands in the hypersurface `f = 0` at the level of
  coordinate algebras.

## Proof as implemented

Evaluation follows the published `traceCoordinate_evaluate`. The published
`AffineCoefficients.universalCharacterMatrix_map` identifies the image of the
universal matrix under evaluation with `ρ(g)`. The coefficient statement then
uses Mathlib's `Matrix.charpoly_map` and `Polynomial.coeff_map`. The
determinant statement uses `RingHom.map_det` together with `map_sub` and
`map_one` for `RingHom.mapMatrix`. Invariance uses the published criterion
`ClassFunctions.mem_algebra_iff_invariant`. For conjugation by a unit `u`,
`Matrix.charpoly_units_conj` applies to the characteristic polynomial. For the
determinant, `1 - u N u⁻¹ = u (1 - N) u⁻¹` and `Matrix.det_units_conj`.

For the vanishing, restriction along `N''` is evaluation at the universal point
of affine `(q + 1)`-space. By `detOneSubCoordinate_evaluate` and
`steinbergModifiedPolynomialMatrix_eq_affineMatrix` it is `det (1 - M)` for the
polynomial matrix `M` of `N''`. This is zero by
`det_one_sub_steinbergModifiedPolynomialMatrix_eq_zero_of_path`.

## Scope

The module identifies neither `f` nor the characteristic-polynomial coefficients
with Steinberg's fundamental characters or with generators of the invariant
algebra. It treats neither `N'''` nor the stratum `f ≠ 0`, and it proves no
isomorphism of `N''` onto `f = 0`. These remain obligations of the host task.
