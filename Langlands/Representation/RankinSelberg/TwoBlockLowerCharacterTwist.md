# Common determinant twists of actual normalized lower block induction

Author: Worker 15.

This is internal algebraic support for the second-block Whittaker deformation
transport. It adapts the published upper-parabolic argument in
`Induction.NormalizedProductCharacterTwist` (Workers 468 and 6) to the actual
lower parabolic, retaining the inverse half-modulus. It asserts no new literal
literature theorem.

For a p-adic field in any field universe, supplied topological data `T`, any
ordered block shape `B`, smooth unit character `χ`, and representations on the
original dependent block carriers in an independent universe,
`Langlands.RankinSelberg.TwoBlockSecondDeformation.lowerTwistEquiv` is an actual
representation equivalence. Its source is the global determinant-character
twist of normalized lower induction; its target is normalized lower induction
of the blocks, each twisted by the same determinant character. No smoothness,
admissibility, irreducibility, or Whittaker-type hypothesis on the blocks is
required.

The published `TwoBlockConvergence.determinant_oppositeParabolic`, imported
from `TwoBlockJacquetConvergence.RadicalIwasawa`, writes the determinant of a
lower block triangular matrix as the product of the determinants of its actual
opposite Levi blocks. The tensor-action comparison restricts the ambient
determinant character to the actual Levi embedding, identifies every coordinate
character, and applies the published `SmoothCharacter.external_coordinate_twist`.
Thus the comparison holds on the complete dependent tensor carrier, preserving
all block sizes and their order.

`lowerTwistInducing_eq` compares the full lower-parabolic covariance actions:
the same inverse half-modulus occurs on both sides and the two scalar actions
commute. The equivalence `lowerTwistEquiv` then composes the published
`smoothInductionTwistEquiv` with smooth induction of the identity linear
equivalence of these coefficient actions. On an actual induced section it
multiplies the value at `g` by `χ(det g)`; covariance, smoothness, inverse laws,
and equivariance come from those constructions.

This module supplies the algebraic representation comparison. It does not
assert a Whittaker deformation, analytic dependence, integral analyticity, or
any factor specialization. The smoothness of a particular determinant power
must be supplied separately when this equivalence is specialized.
