# The actual geometric Borel of a supplied split pinning

For an arbitrary field `k : Type u`, an actual affine group scheme `G` over
`Spec k`, and a supplied complete `SplitPinning G`, `negativeGeometricBorel`
packages an actual group scheme, its inclusion into `G`, and a proof of
`IsGeometricBorelSubgroup` for that inclusion. Its underlying object and
inclusion are exactly `negativeBorel` and `negativeBorelHom` from `SplitBorelCell`.
The latter module constructs the representative of the negative dynamic
parabolic; the present module establishes its geometric Borel property.

`IsGeometricBorelSubgroup` means that the inclusion is Borel over `k` and
remains Borel after pullback to the algebraic closure. Here Borel means a smooth,
connected, solvable closed subgroup, maximal among such subgroups through
actual factorization of inclusions. It is not merely a condition on rational
points.

The proof is an internal consequence of published Library results. First,
`isRegularCocharacter_neg_positiveCocharacter` reverses the chosen positive
cocharacter of the pinning. Its pairing with every actual root is nonzero
because the original cocharacter is generic and negation preserves
nonvanishing.

`isBorelSubgroup_baseChange_negativeBorelHom` proves the stronger intermediate
claim that the actual pullback of this inclusion is Borel over every field
extension `K : Type u` of `k`. The split character-lattice base-change
equivalence writes every extended character as a pullback.
`mem_roots_baseChange_iff` reflects its actual root membership, and
`latticePairing_baseChange` transfers regularity of the reversed cocharacter.
The published field-extension proof supplies connected reductivity, while
`maximalTorusBaseChange` and split-torus base change supply the extended split
maximal torus.

The equality between reversing a multiplicative cocharacter and negating its
lattice element identifies the pulled-back dynamic cocharacter with that
regular cocharacter composed with the extended torus inclusion. Dynamic
parabolic base change and the original representation property therefore
identify the pulled-back inclusion as a representative of its dynamic
parabolic. Clause one of the published `regularCocharacterBorel` proof gives
the Borel property. The closed-subgroup premise comes from the affine dynamic
representative and its actual base change.

Specializing this result to the algebraic closure and applying
`isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure` proves
`isGeometricBorelSubgroup_negativeBorelHom`. The selected
`negativeGeometricBorel` packages precisely these witnesses.
`isBorelPair_negativeBorelHom` uses the original pinning's maximal torus and
its existing factorization through the negative parabolic. Finally,
`isQuasiSplit` combines connected reductivity from the supplied pinning with
the constructed geometric Borel.

The construction retains arbitrary fields and universe `u`, with no
characteristic, perfectness, dimension, or norm premise. It requires a complete
pinning as input. It does not construct such a pinning, a Galois descent datum,
an adjoint quotient, or an unconditional quasi-split inner form; those remain
obligations of the host existence task.
