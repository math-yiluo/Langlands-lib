# Prefix products and interleaved group products

This internal algebraic construction records the finite product identity used
to compare the supplied Steinberg product with its conjugated additive factors.
It is derived directly from the group laws and has no literature dependency.

`Langlands.orderedPrefix r f j` is the product of the first `j` factors of an
ordered family `f : Fin r → A` in a monoid. Its recursive definition starts at
one and strips the first factor. The zero, successor and last lemmas identify
the empty prefix, successive prefixes and the full product. `map_orderedPrefix`
proves compatibility with any monoid homomorphism by induction.

For a group, `interleaved_prod_eq_prefix_conjugates` rewrites the ordered product
of `x j * n j` as the product of `x j` conjugated by the preceding `n` factors,
followed by the full product of the `n` factors. The proof inducts on the number
of factors and uses that conjugation preserves list products. The empty family
is included.
