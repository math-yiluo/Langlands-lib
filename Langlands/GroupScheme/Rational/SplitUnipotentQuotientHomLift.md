# Arbitrary torus homomorphisms through split-unipotent quotients

This internal adapter works over an arbitrary field `k : Type u`. It lifts every
actual torus homomorphism `j : H ⟶ Q` through a specified fppf quotient
`q : G ⟶ Q` with smooth connected split-unipotent full kernel. It retains the
exact stable-vector proposition as an explicit input.

`IsTorus.exists_splitUnipotentQuotientHomLift` assumes affine `G` and `Q`,
smooth connected `U`, a homomorphism `n : U ⟶ G` monomorphic as a relative
scheme morphism, and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q`. This quotient
predicate includes the equality of the full kernel range with the range of
`n` on every test scheme. The remaining inputs are `IsUnipotent U`,
`RelativeRoot.IsSplitUnipotent U`, `IsTorus H`, and
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}`. The conclusion
is an actual group-scheme morphism `l : H ⟶ G` with `l ≫ q = j` over `k`.
There is no closed immersion condition on `j`.

`IsTorus.splitUnipotentQuotientHomLift` chooses such a lift, and its `_comp`
theorem records the prescribed equation. Over a perfect field,
`IsTorus.exists_perfectFieldUnipotentQuotientHomLift` assumes additionally
that `U` is affine and uses the published `perfectFieldUnipotentSplit` proof
to supply splitness. The cocharacter corollary specializes this result to
the actual multiplicative group torus over `k`. Every cocharacter in that
conclusion and its lift are defined over the same original field.

The construction forms the actual pullback group scheme of `q` and `j`.
Affineness of `G` and `Q` makes `q` affine and quasi-compact. The smooth
represented full kernel makes `q` smooth, and its actual kernel is smooth,
affine and connected. Its geometric connectedness gives connectedness of the
pullback over the connected torus. The pullback projection is affine by base
change of `q`, so the pullback group is affine over the field without any
closedness condition on `j`. Smoothness and surjectivity of this projection
also follow by base change. Its full kernel is canonically isomorphic to the
original full kernel, preserving connectedness, unipotence and splitness.
The published split-unipotent extension section theorem then supplies a
homomorphic section. The published torus action linearization proof supplies
its linearization input; the stable-vector input remains explicit.
Composing the section with the other pullback projection gives the required
lift, and pullback commutativity proves its equation.

The provenance is internal: this adapts the published closed-torus pullback
construction and extension-section theorem to arbitrary torus homomorphisms
using affine base change. Worker 1459 suggested the pullback-section route.
No additional external structural assertion is introduced. The stable-vector
proof and the finite-field central-cocharacter solvability theorem remain
separate obligations.
