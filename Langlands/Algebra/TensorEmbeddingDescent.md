# Descent detected by an embedding of field algebras

This internal algebraic lemma supports descent along a dominant affine
parametrization in the split geometric radical proof. It is a derived result,
not a statement attributed verbatim to Springer.

For an injective map of algebras `A → B` over a field `k`, a tensor in
`K ⊗[k] A` comes from `A` whenever its image in `K ⊗[k] B` comes from `B`.
Here `K` is any nonzero commutative `k`-algebra. Consequently an algebra map
into `K ⊗[k] A` has a unique descent when its composite into
`K ⊗[k] B` descends.

`descendAlgHom` chooses this unique descended algebra map, and
`includeRight_comp_descendAlgHom` verifies that extending its coefficients
recovers the supplied map.

The proof chooses a `k`-linear left inverse of `A → B`, tensors the left
inverse, and applies it to the given equality. For algebra maps, it restricts
the range to the image of `A` and uses the algebra equivalence with that image.
Injectivity of `A → K ⊗[k] A` proves uniqueness. The result does not construct
the solvable torus quotient or establish its kernel geometry.
