# Actual diagonal characters on triangular additive coordinates

This internal construction works over any commutative ring `R`, in arbitrary
universe `u`, with every matrix size `N`. It uses the actual diagonal block Levi
for the weights `i ↦ -i`, an arbitrary commutative group scheme `D`, and an
actual homomorphism from `D` to that Levi. No smoothness, connectedness,
reducedness, or torsion-free character assumption is made.

`diagonalEntryPoints` evaluates one diagonal coordinate using the all-test
unit-valued model of the diagonal Levi. Its proved naturality gives the actual
group-scheme homomorphism `diagonalEntryHom` by Yoneda.
`diagonalEntryHom_value` identifies its multiplicative-group value with the
corresponding matrix diagonal entry on every relative test scheme.

`diagonalRatioCharacter d i l` restricts the quotient of diagonal entries
`i` and `l` to `D`. It is an element of the existing `characterLattice D`,
which is defined for an arbitrary commutative group scheme.
`diagonalRatioCharacter_value` expresses its value as the `i` diagonal entry
of the image matrix times the `l` diagonal entry of its inverse.

Given a triangular homomorphism `j : H → B`, a homomorphism `q : H → D`,
and the actual factorization `q ≫ d = j ≫ blockLimitHom`,
`diagonal_factor_entry` proves that diagonal projection preserves the original
matrix diagonal entries on all relative points. The proof uses the published
all-test formula for `blockLimitHom` and its block-diagonal projection.
`diagonalRatioCharacter_value_lift` therefore evaluates the ratio character
at an arbitrary lifted point of `H` in terms of its original matrix.
No quotient or surjectivity condition on `q` is required here.

`filtrationConjugation j a b` is the actual action of `H` on the full
coordinate-refined subgroup `filtrationScheme` of its representation.
The proved normality of this subgroup and its closed inclusion supply the
normal-conjugation construction. `filtrationConjugation_comp` gives its
ambient formula `g x g⁻¹` on every relative test scheme.

`filtrationCoordinate_equivariant` states that each actual one-dimensional
additive coordinate intertwines this action with the weight action of the
ratio character, after `q`. It holds for every `a`, `b`, and pair of matrix
indices `i`, `l`; a coordinate may be zero. The proof compares vector-group
coordinates, uses the explicit matrix-layer conjugation formula at the
inverse of the acting upper-triangular matrix, and substitutes the preceding
ratio evaluation. A commutative-ring identity then identifies the two values.
All tests use the original coefficient ring, including nonreduced test schemes.

The provenance is internal: these are direct consequences of the actual
Levi point model, Yoneda, block projection, the previously constructed full
coordinate subgroups and additive maps, and the matrix-layer calculation.
This module proves coordinate equivariance. It does not construct diagonal
images or normal quotients, assemble a quotient tower, or prove the final
splitting statement; those remain separate obligations.
