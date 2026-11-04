# Convolution algebra points under scalar extension

For a commutative bialgebra `C` over a field `k`, a commutative
`k`-algebra `R`, and a commutative `R`-algebra `A` with the compatible
`k`-algebra structure, restriction along `c ↦ 1 ⊗ c` identifies the
`R`-algebra maps `R ⊗[k] C → A` with the `k`-algebra maps `C → A`.
The inverse sends a map `f` to the map `r ⊗ c ↦ r • f c`.

Assuming that group-like elements span `C`, `baseChangeMulEquiv`
bundles this identification as an equivalence of convolution monoids.
To prove multiplication preservation, the code checks equality on the
group-like basis. Each basis vector and its scalar extension are
group-like, so convolution on both sides is the product of the two
values. No integral-domain hypothesis on `R` is required here.
The restriction is also natural under every `R`-algebra map of
coefficient algebras. The rings and algebras have independent universes.

This is an internal algebraic derivation from the tensor-product
universal property and the published group-like basis construction.
