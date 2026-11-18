# Wound unipotent groups over perfect fields are finite

`Langlands.GroupScheme.perfectFieldWoundUnipotentFinite` proves
[`PerfectFieldWoundUnipotentFiniteStatement`](PerfectWoundFiniteStatement.md)
in every universe. For a smooth affine connected unipotent group scheme over
a perfect field, every affine-line morphism is constant if and only if the
structure morphism is finite. The proof also shows that either condition makes
the structure morphism an isomorphism.

## Lean proof

For the forward implication, `perfectFieldUnipotentSplit` supplies a split
unipotent series for the group. The published lemma
`HasConstantAffineLineMaps.hom_eq_zero_of_isSplitUnipotent` applied to the
identity homomorphism identifies it with the zero homomorphism. On underlying
schemes the zero homomorphism is the structure morphism followed by the
identity section. The section is therefore a two-sided inverse to the
structure morphism, which is finite because it is an isomorphism.

For the reverse implication, a finite scheme over a field is locally Artinian
and has discrete underlying topology. Connectedness makes its space a
singleton, so the identity section is surjective. The identity section is a
closed immersion, and smoothness makes its target reduced. Thus the identity
section, and hence the structure morphism, is an isomorphism. Every morphism
from the affine line then equals the structure morphism of the affine line
followed by the identity section, by cancellation over the base.

## Source

J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017,
Definition 14.69 and 14.70, printed pp. 299–300, registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The forward implication uses the splitting result of 14.63, which in positive
characteristic uses Corollary 14.55.
The argument through vanishing of the identity homomorphism and the argument
through the reduced finite scheme are the formal proof routes used here.
