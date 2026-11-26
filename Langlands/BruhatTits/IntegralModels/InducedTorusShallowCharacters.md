# Normalized character depths in the coordinates of an induced torus

`InducedTorusShallow.geometricCoefficientEquiv` is the geometric embedding
decomposition of the coefficient algebra of a finite product of finite
separable extensions of the maximal unramified field. It distributes tensor
product over the finite product, applies `WeilGm.separableEmbeddingDecomposition`
in each factor, and combines the two indices into the set of pairs consisting
of a factor and an embedding of that factor. The map sends a pure tensor
\(c\otimes b\) to the function \((i,\tau)\mapsto c\tau(b_i)\).

`InducedTorusShallow.mem_geometricCharacterCongruence_iff` identifies the
full published geometric-character test on the rational Weil restriction
with the condition that the normalized additive value of each unit
coordinate minus one is at least the given positive depth. For the split
torus, projection onto each multiplicative group gives necessity. The
product decomposition by the coordinate cocharacters gives sufficiency.
The geometric coefficient equivalence then identifies the split coordinates
with the embedding values of the original units.
`MaximalUnramified.coordinateEmbedding_preserves_value` identifies the
normalized values for all embeddings with the values at the inclusions.

This comparison formalizes the coordinate calculation in the proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition
B.3.6(1), printed p. 659 (one-based PDF p. 690), using the tensor
representation of the actual Weil restriction. The registered literature
ID is `kaletha-prasad-2023-bruhat-tits-new-approach` and the SHA-256 is
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
