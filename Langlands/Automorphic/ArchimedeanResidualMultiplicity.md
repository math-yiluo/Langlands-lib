# Separating a compact and Lie factor with commuting residual operators

This internal construction for the proof of
`CuspidalTransposeInverseContragredientStatement` extends compact and Lie tensor
evaluation to a target with an arbitrary indexed family of remaining
operators commuting with the chosen compact and Lie actions. It provides
a tensor equivalence and proves irreducibility of the residual
multiplicity space under those remaining operators. The target need not
be an actual automorphic subspace, allowing the construction to be reused
after a factor is removed.

The source satisfies the published `GKModuleDensity.Hyp`. The target is
nonzero and irreducible under its chosen compact and Lie actions together
with the supplied remaining operator family. The simultaneous
intertwiner space is also assumed nonzero. Each remaining operator acts
on this space by the existing commuting postcomposition construction.

Tensor evaluation is injective by genuine compact and Lie Jacobson
density. Its range is stable under the local actions and every remaining
operator. Evaluation at one nonzero source vector is injective on
intertwiners, so the assumed nonzero intertwiner space makes that range
nonzero. Joint irreducibility of the target makes it the entire target,
giving the tensor equivalence.

For residual irreducibility, a nonzero residual-stable subspace `N` gives
an evaluation image of `V ⊗ N` stable under all three target operator
families. This image is again the whole target. Tensor evaluation is
injective, so a preimage of `f(v)` must be `v ⊗ f`. Contraction with a
linear functional equal to one at `v` shows that every residual
multiplicity `f` lies in `N`.

All group, Lie algebra, carrier and operator-index universes are free.
No existence of a local factor or an invariant pairing is asserted.
