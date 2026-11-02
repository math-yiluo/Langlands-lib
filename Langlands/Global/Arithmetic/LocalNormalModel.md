# Rational models of local normal closures

For any prime `p` and any supplied finite p-adic field `E : PadicField p`,
`localNormalClosure p E` is the normal closure of `E.Carrier` over `Padic p`
inside `AlgebraicClosure E.Carrier`. The original field embeds by its
algebra structure, and the p-adic algebra structures form a scalar tower.
Mathlib's normal-closure construction supplies finite dimensionality and
normality. Characteristic zero follows from the injective p-adic algebra map;
separability in characteristic zero makes the closure Galois.

`localNormalModel p E` applies the rational splitting model to this finite
Galois field. It is a number field in `Type 0`, Galois over the rationals and
totally real, independently of the universe of `E.Carrier`.
`localNormalModelEmbedding` is its ring embedding in the local normal closure.
The theorem `localNormalModelEmbedding_adjoin` says that adjoining the image
to the p-adic scalars gives the entire normal closure.

This is an internal derived specialization of `RationalGaloisModel`, using
Mathlib's normal closure rather than making additional literature claims.
The algebraic closure contains the actual supplied field, so no replacement
of that field or restriction on its universe is needed. This construction
does not yet choose global intermediate fields, finite primes, completion
isomorphisms or an action comparison for the original local extension.
