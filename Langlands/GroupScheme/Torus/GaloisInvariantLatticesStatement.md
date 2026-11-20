# Rational characters and cocharacters as Galois invariants

`GaloisInvariantLatticesStatement.{u}` concerns a Galois extension `K/k`
and an affine commutative group scheme `T` over `Spec k`. The extension
may be infinite. Both maps `baseChangeToInvariants k K T` are bijective.
These are the existing integer-linear maps from the character and
cocharacter groups over `k` to the respective submodules fixed by
`Gal(K/k)` after base change. The action is transport along coefficient
automorphisms on the actual homomorphisms to and from `𝔾ₘ`.

## Provenance

Milne, *Algebraic Groups* (2017), §12.g, printed p. 239 (PDF p. 255),
identifies rational characters with the Galois invariants of the
separable-closure character group. The Lean statement gives the
commutative affine scope and the corresponding cocharacter assertion.
It also quantifies over arbitrary Galois extensions, with the absolute
case obtained by taking `K = SeparableClosure k`. These are instances
of descent of actual group-scheme homomorphisms. The registered source
is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
