# Adjoint weight projections and generic cocharacters

Author: Worker 74.

This internal module concerns the actual adjoint representation on
`Additive (lieKernel G k)`, as constructed in `Lie.Adjoint`. It is derived from
the all-test-algebra weight-space definition and the published split-torus
weight decomposition. It adds no structural assumption about centralizers.

`weightComponentProjection q hq j` is the linear projection onto summand `j` of an
internal direct-sum decomposition `q`. It first uses the decomposition's linear
equivalence, extracts component `j` and includes that submodule in the ambient module.
Its two evaluation lemmas prove that it fixes vectors in that summand and vanishes on
every other summand. `weightSpaceProjection hT i χ` specializes this construction to
the actual adjoint character weight spaces of a split torus, for an affine group scheme
locally of finite type over a field. Its corresponding evaluation lemmas have the same
form. The construction uses classical choice of a decomposition; it has no added
centralizer hypotheses.

Restricting the acting commutative group along a homomorphism sends a
character weight space into the weight space for its pulled-back character.
For an affine group scheme locally of finite type over a field, both the
split-torus action and the restricted multiplicative-group action have
internal weight decompositions. The component-projection construction applied to the latter action's zero
weight space kills every original weight with nonzero restriction.

If the cocharacter is generic, a nonzero original character that restricts
to zero has zero weight space: otherwise it would be a relative root
contradicting genericity. The projection argument therefore identifies the
two zero weight spaces. The proof uses group characters, so this argument
also applies in positive characteristic.

The resulting theorem is a Lie-algebra statement. It does not identify the
group-scheme centralizers, establish their smoothness or connectedness, or
prove `GenericCentralizerStatement`.
