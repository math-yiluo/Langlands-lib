# Infinite-Galois descent of tensor ideals

This is an internal algebraic adapter for the stable-submodule descent proved
in `Langlands.LinearAlgebra.GaloisSubmoduleDescent`. Let `K/k` be a Galois
extension, possibly infinite, and let `A` be any commutative `k`-algebra.
`groundIdeal` contracts an ideal of `K ⊗[k] A` along `a ↦ 1 ⊗ a`.

If an ideal is stable under every coefficient conjugation from
`TensorGaloisPoint`, `map_groundIdeal_eq` proves that extending its contraction
recovers it. Choose an arbitrary basis of `A`, pass to its scalar-extended
coordinate basis, and apply the stable-submodule spanning theorem. Each
ground-field coordinate vector is the image of the corresponding element of
`A`. Since the extended contracted ideal is closed under extension-field
linear combinations, it contains the original ideal. The opposite inclusion
is the ordinary extension-contraction inequality.

Consequently, two algebra maps out of the tensor algebra that agree on `A`
give equal extensions of the invariant ideal. This statement includes arbitrary
nonreduced algebras and makes no finite-dimensionality or finite-generation
assumption. It is an ideal-level result; it does not itself construct a group
scheme or prove that a particular geometric subgroup has an invariant ideal.
