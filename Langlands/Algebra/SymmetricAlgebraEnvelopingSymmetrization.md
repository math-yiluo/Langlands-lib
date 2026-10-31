# Symmetrization from the whole symmetric algebra

For a field `R : Type` and an `R`-Lie algebra `L` in any universe,
`symmetricAlgebraSymmetrize` is an `R`-linear map from Mathlib's actual
`SymmetricAlgebra R L` into the genuine `UniversalEnvelopingAlgebra R L`.
It sends a monomial of degree `d` to the average of all ordered products of
its genuine Lie generators, with coefficient the inverse of `d!` in `R`.
It is a linear map; multiplicativity is not asserted.

The intermediate `tensorSymmetrize` uses Mathlib's actual tensor-algebra
isomorphism with the direct sum of tensor powers. On each tensor power it
applies the tensor universal property to the already constructed
`symmetricWord`, then sums the finitely supported components. Its value on a
pure tensor-algebra product is `symmetricWord`. `tensorWord` denotes an ordered
list product of the tensor-algebra generators. The two linear-map
extensionality lemmas establish that these generator words, equivalently all
pure tensor-algebra products, determine every linear map out of the tensor
algebra: compose with the map from the direct sum and use pure-tensor
extensionality on each summand.

Quotient descent checks the defining symmetric-algebra relation inside
arbitrary left and right tensor-algebra contexts. First an explicit
permutation of `Fin (m + n + 2)` swaps the two marked adjacent entries and fixes
both context tuples. Permutation invariance of `symmetricWord` therefore proves
`tensorSymmetrize_word_context_swap`. Applying linear-map extensionality to
each context proves `tensorSymmetrize_context_swap` for arbitrary tensor-algebra
contexts. Induction on the generated ring congruence proves
`tensorSymmetrize_context_congr`: addition follows by linearity, and a product
relation is handled by substituting its two factors successively with the
other factor absorbed into a context. Setting both contexts to one makes
`tensorSymmetrize` well-defined on the actual symmetric-algebra quotient.
Quotient induction proves its additivity and scalar compatibility.

`symmetricAlgebraSymmetrize_algHom` identifies the descended map with the total
tensor map on quotient representatives. `symmetricAlgebraSymmetrize_prod`
evaluates every generator monomial, including the empty monomial. Separate
formulas show that one, scalar constants, and Lie generators are sent to their
actual enveloping counterparts. `symmetricAlgebraSymmetrize_prod_mem` places a
monomial's image in the genuine enveloping filtration piece indexed by its
length. In characteristic zero,
`symmetricAlgebraSymmetrize_prod_sub_word_mem` places the difference from its
ordered enveloping word in degree at most length minus one, by the previously
proved permutation-average comparison. At length zero the difference is zero.

`map_tensorSymmetrize` and `map_symmetricAlgebraSymmetrize` prove naturality
under any `R`-algebra map between the genuine enveloping algebras compatible
with a specified `R`-linear map on their Lie generators. The tensor statement
is checked on pure products. The quotient statement uses surjectivity of the
tensor-to-symmetric quotient and the commuting square of the actual algebra
maps induced by that linear map. No injectivity or separate Lie-map hypothesis
is assumed beyond the stated compatibility. The construction and naturality
hold in any characteristic; if the characteristic divides `d!`, the inverse
coefficient and the degree-`d` average are zero. Only the strict lower-degree
comparison requires characteristic zero.

This is internal, derived algebraic infrastructure. Its provenance is the
actual tensor-algebra direct-sum equivalence, the defining symmetric-algebra
ring congruence, the tensor universal property, and the previously constructed
normalized symmetric words and genuine enveloping filtration. It asserts no
isomorphism between the symmetric algebra and the direct sum of symmetric
powers, no injectivity or surjectivity of whole symmetrization, no filtered
central generation, and no automorphic differential-growth theorem.
