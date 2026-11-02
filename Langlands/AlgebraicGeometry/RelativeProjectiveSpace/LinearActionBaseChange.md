# Coefficient base change for actual projective linear actions

`ProjectiveSpace.coefficientMap n φ` exposes the existing polynomial-Proj
coefficient map for an explicit ring homomorphism `φ : K →+* R`.
The map is contravariant in `φ`, commutes with the structural morphisms
to the ring spectra, and is compatible with projection to the integral
polynomial model.

If two specified invertible linear maps on `K^(n+1)` and `R^(n+1)`
have matrix coefficients related by `φ`, their actual projective scheme
actions commute with this coefficient map. This conclusion is an equality
of scheme morphisms. It uses the complete matrix coefficient condition,
with no field or injectivity hypothesis on `φ`.

For any scheme equipped with compatible maps to `Spec K` and `Spec R`,
the two resulting relative projective actions are equal. More generally,
the actions commute with a simultaneous change of scheme base and
coefficient ring, under the stated compatibility of the base maps and
matrix coefficients. In particular, this comparison can be used when
restricting a coefficient matrix to an open subscheme; the equivalence
over the new coefficient ring remains an explicit input.

These results are internal consequences of existing constructions.
The coefficient map is the existing `ProjSpace.map` for the algebra
structure induced by `φ`. Its identity and composition follow from
polynomial coefficient-map functoriality and `Proj.map` functoriality.
The existing Cartesian square gives its structural comparison.
Polynomial ring-homomorphism extensionality on constants and variables
shows that coefficient mapping commutes with the two substitutions.
`Proj.map_comp` then gives the actual projective action square.
The relative results follow from the affine comparison and uniqueness
using the base and polynomial projections. No additional external source
assertion is used.
