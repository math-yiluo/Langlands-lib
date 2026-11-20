# Affine Weil restriction from a finite product of algebras

Let `B` and the `D i` be finite projective commutative algebras over a
commutative ring `A`, with finitely many indices `i`. Suppose the specified
`B`-algebra structures on `D i` are compatible with their `A`-algebra
structures and the product of the maps `B → D i` is bijective. Let `H` be an
affine group scheme over `Spec B` whose structural map is locally of finite
type. Each factor is the actual pullback of `H` to `Spec (D i)`.

`AffineWeil.AlgebraProduct.tensorIso` identifies `B ⊗[A] R` with the product of
`D i ⊗[A] R` for each affine test algebra `R` over `A`, retaining the original
`B`-action. The pure tensor `b ⊗ r` maps to the family `(bᵢ ⊗ r)ᵢ`, where `bᵢ`
is the image of `b` in `D i`. This formula verifies compatibility with a
change of test algebra.

Apply this equivalence to the actual tensor-valued points of `H`. The
multiplicative comparison for the pullback adjunction identifies the `i`-th
component with points of the pullback to `Spec (D i)`, over the tensor algebra
`D i ⊗[A] R`. These are the `R`-points of the `i`-th affine Weil restriction.
The resulting family of equivalences is natural in `R` and yields the actual
group scheme isomorphism `AffineWeil.AlgebraProduct.iso` between the Weil
restriction from `B` and the product of the component Weil restrictions.
This is an internal construction used for the number-field Hasse reduction.
