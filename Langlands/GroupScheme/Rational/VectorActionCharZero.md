# Scalar linearity of vector actions in characteristic zero

This is an internal consequence of the existing actual action and natural
vector-coordinate constructions. Let `k : Type u` be a field, let `H` and `V`
be actual group schemes over `Spec k`, let `b` be an actual automorphic action
of `H` on `V`, and let `d` be any natural number. The supplied family `e`
identifies every scheme-test point group of `V` with the additive group of
`d`-tuples of global functions. Naturality of `e` is a separate hypothesis.

`IsAffineLinearVectorCoordinates b e` records scalar compatibility in
`vectorAffineCoordinates e A` for every commutative coefficient `k`-algebra
`A`, every acting point in `H(A)`, every vector point in `V(A)`, and every
scalar in `A`. This predicate by itself does not assert naturality.

The private polynomial lemma compares coefficients in the identity
`p(2 X) = 2 p(X)` over an arbitrary algebra over a characteristic-zero field.
For every degree other than one, the coefficient is annihilated by
`2^n - 2`. This is the image of a nonzero field element and is therefore a
unit, including when the coefficient algebra is trivial. Thus `p` is exactly
its linear term.

`isAffineLinearVectorCoordinates_of_charZero` proves the coefficient-test
predicate from `CharZero k` and naturality of `e`. No affineness assumption on
`H` or `V` is needed at this stage. Conjugating the actual action by the
coordinate equivalence gives an additive map on coordinate tuples, natural
under every coefficient map. Fix an acting point and a tuple `x` over `A`.
Over `A[X]`, act by the constant acting point on the tuple `X * x`. Each
output coordinate is a polynomial `P`. Naturality under substitution
`X` by `2 X`, and additivity of the action, give `P(2 X) = 2 P(X)`.
The polynomial lemma makes `P` linear. Naturality under evaluation at an
arbitrary scalar and at one then proves scalar compatibility. This treats
nonunit scalars and algebras with nilpotents.

`IsNaturalVectorCoordinates.vectorAffineCoordinates_unit_comp` identifies
the coefficient coordinates of a point on the relative affinization of any
test `T` with the coordinates of its pullback to `T`. The proof uses
naturality of `e` and the existing identity for global functions pulled back
along the affinization unit.

`IsAffineLinearVectorCoordinates.isLinearVectorCoordinates` upgrades the
coefficient-test predicate and naturality to the existing all-test
`IsLinearVectorCoordinates` predicate when `H` is affine. The acting point
factors through the relative affinization of `T`. The inverse coordinate
equivalence on that affine test supplies the vector point and its scalar
multiple; the preceding unit-coordinate identity identifies their pullbacks
with the original point and its scalar multiple. Pulling back the
coefficient-test identity, using naturality of the actual action, proves
scalar linearity over the ring of global functions of `T`. This upgrade is
valid over every field and does not require `V` to be affine.

Finally, `isLinearVectorCoordinates_of_charZero` combines the two steps:
when `k` has characteristic zero and `H` is affine, every actual automorphic
action is linear in any supplied natural vector coordinates on every scheme
test. All results retain arbitrary universe `u`, allow `d = 0`, and include
nonaffine and empty tests in the all-test conclusions.

This development does not construct vector coordinates on a commutative
unipotent group, prove characteristic-positive torus linearization, or prove
the central-vector or ordered-product targets. Those remain separate
obligations.
