# Characters of finite groups of prime-to-characteristic order

This internal helper for `EtaleMultiplicativeTypeOrderStatement` proves that
characters of a finite commutative group `M` with values in the units of a
separably closed field `K` distinguish its elements when `Nat.card M` is coprime
to the characteristic exponent `p` of `K`. Its provenance is the finite abelian
group duality argument in Mathlib, applied to the converse direction of the
corrected last sentence of Milne, *Algebraic Groups* (2017), Example 12.28.
The unchanged target statement's Markdown documents the source correction.

First, `cast_ne_zero_of_coprime` splits characteristic zero from prime
characteristic. A positive integer prime to `p` has nonzero image in `K`.
The exponent of `M` is positive and divides its order. Its image in `K` is
therefore nonzero, and Mathlib's separably closed field instance supplies
`HasEnoughRootsOfUnity K (Monoid.exponent M)`.

Mathlib's finite abelian duality then gives `exists_apply_ne_one` and
`forall_apply_eq_apply_iff`. Finally, `exists_separating_family` chooses a
character detecting each nonidentity element, with an arbitrary character at
the identity. If two points have the same values under that family, the
character assigned to their quotient forces them to be equal. The indexing set
is `M` itself, so this family is finite.
