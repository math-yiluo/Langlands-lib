# Determinant character of an actual finite Lie action

For an automorphic action `a : AutomorphicAction H U` over any commutative ring,
with affine `U` and natural finite coordinates `c : Lie.FiniteCoordinates U d`,
`coordinateMatrix_det` identifies the determinant of the constructed coordinate
matrix with `LinearEquiv.det (a.differential h)` on the actual Lie module
`Additive (lieKernel U A)`. The proof first identifies its coordinate linear
map with matrix multiplication. It then uses the determinant of that linear
map and invariance under conjugation by `c.equiv A`. The construction permits
`d = 0`, arbitrary characteristic and arbitrary, possibly nonreduced, test
algebras. The determinant naturality theorem follows by applying matrix
determinant to the previously established matrix naturality.

If the acting group scheme `H` is affine, `determinantCharacter a c` is the
rational character obtained by composing the actual morphism
`a.finiteRepresentation c : H ⟶ GL_d` with the published morphism
`GeneralLinear.determinantCharacter : GL_d ⟶ Gm`. In Lean this composition uses
`characterRestrict`. Neither the representation nor the character is supplied
as a field of the coordinate datum.

`determinantCharacter_eval` evaluates this character on every scheme test as
the determinant of the representation matrix in global sections. Its affine
specialization `determinantCharacter_eval_affine` is the determinant of the
actual differential, transported into global sections by the canonical
inverse affine section comparison. Finally,
`determinantCharacter_affinePoints` reads the actual Gm-valued morphism through
`Gm.affinePointsEquiv` and obtains exactly
`LinearEquiv.det (a.differential h)` in the units of `A`. This last proof
cancels the canonical spectrum/global-sections comparison. The formulas hold
for every commutative test algebra; `differential_det_naturality` handles every
algebra map, including scalar extensions to fields.

This is an internal construction from the published actual differential,
finite algebraic representation, general linear determinant and determinant
invariance under change of linear coordinates. It makes no structural
smoothness or finite-dimensionality claim about dynamic subgroups: finite
coordinates are the explicitly stated input of this unit. For normalized
conjugation the original action retains orientation `h*u*h⁻¹`. No absolute
value, Haar measure, square root or analytic modulus is used.
