# Special twists compatible with the embedded integer subfield

Fix the embedded integer subfield used in the special tangent condition.
`ConjugationSubfieldFactorization` says that on this subring, inverse
conjugation by a division unit agrees with precomposition by a ring
automorphism of the embedded integers followed by inverse conjugation by an
integer-order unit. Every integer-order unit satisfies the condition, as does
a division unit whose conjugation restricts to a specified automorphism of
the embedded integers.

Under this order-algebra hypothesis, `twistOfSubfieldFactorization`
constructs the special coordinate module or atlas with the actual
conjugated order action. The existing integral twist isomorphism transports
the tangent basis to the action of the integer-order unit. The restriction
equation then replaces each character by its composition with the subfield
automorphism. These characters remain pairwise distinct by surjectivity of
the automorphism. The construction applies at every geometric fibre.

The underlying laws and covers are preserved, so all scalar-kernel rank
certificates in the height condition carry over. Coefficient extension
commutes with the special twists, and the atlas recovers the earlier
integral special twist for an integer-order unit. The whole atlas
quasi-isogeny to the new special order action is the existing
`atlasTwistQuasiIsogeny`.

This is a sufficient criterion for the special twist in Drinfel'd,
*Coverings of p-adic symmetric regions* (1976), §2 A, printed p. 109.
Establishing the criterion for arbitrary division units and calculating
the change in framing height remain further work.
