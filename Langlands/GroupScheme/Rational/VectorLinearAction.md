# Linear vector actions and their actual differentials

This is an internal helper derived from the existing actual action, Lie kernel,
and vector-coordinate interfaces. Let `k : Type u` be any field, `H` and `V`
actual group schemes over `Spec k`, and `d` any natural number. Suppose `e` gives
multiplicative coordinates on every test scheme, with coordinate addition as the
group operation. The hypothesis `IsLinearVectorCoordinates b e` means that these
coordinates are natural and that the actual action `b` commutes with scalar
multiplication by every global function on every test scheme.

`IsLinearVectorCoordinates.actionLinearEquiv` constructs the actual linear
automorphism on coordinate tuples over every test scheme's ring of global
functions. Its forward map is the action conjugated by `e`; its inverse uses
the inverse acting point. The action laws give the two inverse identities,
the group equivalences give additivity, and the supplied scalar law gives
linearity.

`IsLinearVectorCoordinates.vectorAffineCoordinates_smul` translates this
scalar-linearity law to the coefficient-algebra coordinates
`vectorAffineCoordinates e A` on `V(A)`. The proof pulls a scalar of `A` back
through the inverse of `Scheme.ΓSpecIso`, uses the supplied all-test law, and
pushes forward through its ring-homomorphism component. It applies to every
commutative `k`-algebra and every `H(A)` point, including nonunit scalars.

`vectorLiePoint_eq_epsilon_smul` identifies the actual pure-epsilon kernel point
of a vector with epsilon times its constant lift in vector coordinates. This
uses only naturality of `e`, the previously constructed pure-epsilon point, and
multiplication in the dual-number ring; affineness is not needed for this lemma.

Assume also `IsAffineHom V.X.hom`, so that the actual Lie kernel has the Library's
module structure and its natural linear coordinates `vectorLieCoordinates`.
`IsLinearVectorCoordinates.vectorLieCoordinates_differential` proves that the
coefficients of the differential acting on a vector's pure-epsilon point equal
the coefficients of the original action on that vector. Indeed, the differential
acts by the constant lift of the `H(A)` point. Substitute the epsilon-times-
constant formula, apply scalar-linearity over the dual numbers, and use action
and coordinate naturality for the constant coefficient map. Taking the epsilon
coefficient gives exactly the original action's coordinate tuple.

Finally, `IsLinearVectorCoordinates.coordinateAction_eq` expresses this equality
using the existing `AutomorphicAction.coordinateAction` and
`finiteLieCoordinatesOfVector`. Every tuple is the coordinate tuple of its
inverse-coordinate point, so the preceding identity applies to every tuple.
All statements retain arbitrary universe `u` and include `d = 0`.

This helper supplies the comparison needed to transfer Lie representation
calculations to a given linear vector action. It does not construct a
homogeneous basis or diagonalize a torus action, identify semigroup subgroups,
or prove the full `SemigroupOrderedProductStatement`.
