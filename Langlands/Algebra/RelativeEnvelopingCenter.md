# The centre map from a triangular enveloping decomposition

`RelativeEnvelopingDecomposition` takes an algebra homomorphism `j`
from the Levi algebra into an ambient algebra and a right ideal `I`
in the ambient algebra. The defining conditions say that the
preimage of `I` under `j` is zero, that left multiplication by the
image of `j` preserves `I`, and that every ambient central element
has a representative from the Levi algebra modulo `I`.

For `centerProjection`, the zero preimage gives uniqueness of the
representative. Commuting with the Levi algebra shows that the
representative is central there. The two stability properties prove
multiplicativity of the projection.

This derived construction is applied to the enveloping centre on
Levi constant-term slices. Langlands (1979), Lemma 4, states automorphy
of those slices and gives references for local Hecke admissibility.
See printed p. 204 (Corvallis Part I, PDF p. 199). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
