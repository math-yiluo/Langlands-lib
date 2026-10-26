# Full modulus calculation for flattened refinements

`PadicField.TopologicalData.composedLeviModulus_flattened` proves the equality
of actual positive full modulus characters

`(T.composedLeviModulus B S).comp (flattenedLeviEquiv F B S).toMonoidHom
= T.leviModulus (B.flatten S)`.

It applies to every ordered block shape and refinement over the given p-adic
field, including rank zero. The equivalence in the pullback maps the flattened
product Levi to the actual refined subgroup of the coarse product Levi.
No modulus equality or normalization certificate is assumed.

The proof uses the existing determinant-product definitions. First,
`determinant_leviEmbedding` computes the determinant of the actual embedded
block diagonal matrix. Simultaneous reindexing preserves the determinant;
Mathlib's block triangular determinant formula expresses it as the product
of the determinants of the diagonal blocks. The explicit equivalence from
each block's finite index type to its corresponding fiber identifies every
diagonal block. Applying the actual residue-normalized absolute value gives
`determinantNorm_leviEmbedding`.

The flattened coordinate formulas identify every inner matrix with its
flattened component, with transport along the proved equality of their
sizes. A determinant norm is unchanged by this transport. Consequently, the
norm of each outer determinant is the product of the norms of its inner
determinants, and `refinedLeviBlock` extracts exactly those inner matrices.

For a fine pair with determinant norms `a` and `b` and respective sizes
`d` and `e`, its full modulus factor is `a^e / b^d`. The proved ordering
of flattened blocks is lexicographic. `lexProduct` splits all ordered
fine pairs into pairs in distinct outer blocks and pairs in the same
outer block. In distinct outer blocks, `rectangularProduct` combines
the factors using finite products and sums of natural exponents. The
inner block-size sums equal the outer block sizes, so these are exactly
the outer modulus factors. The remaining factors give the product of
the inner moduli. Their product is the defined composed full modulus.
The final argument proves equality of monoid homomorphisms pointwise.

This is an internal calculation from the published block-coordinate,
determinant, absolute-value and character constructions. It attributes no
additional theorem to external literature. Empty finite products cover the
rank-zero case. This helper is the single raw character calculation shared
by flattened normalization comparisons; it does not claim a separate exact
proof of a statement declaration that has yet to enter the Library.
