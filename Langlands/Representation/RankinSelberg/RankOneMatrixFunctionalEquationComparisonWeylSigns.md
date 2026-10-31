# Explicit rank-one Weyl signs

This internal algebraic helper uses the actual unsigned `weylLong` and
`blockWeylAt` and the published character-change diagonal. It defines
`T = diag((-1)^n,...,-1,1)`, `E = diag(-1,1,...,1)`,
`w = J T` and `w' = T E B`, where `B = blockWeylAt 0 n`.

The inverse and inverse-transpose identities for `T` reuse
`characterChangeElement_neg_one_inv` and
`inverseTranspose_characterChangeElement_neg_one` from `EqualRankSwapTransport`
through the specialized wrapper names. The implemented proof shows that `T` and
`E` square to the identity and `E` commutes with `B`. Multiplicativity of
inverse transpose then gives `(w g^iota w') E = J (T g T)^iota B`.
This is finite matrix and group algebra over an arbitrary field.

The provenance is internal derivation over the published matrices. This
helper does not assert a weighted integral comparison or a gamma equation.
