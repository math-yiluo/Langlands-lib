# Coefficient ideals for projective tensor factors

This internal algebra unit supports the closed fixed-locus construction of
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015),
Proposition A.8.10(1), printed pp. 547–549. It formalizes a derived algebraic
step, rather than a representability theorem.

For a commutative ring R, an R-module P, and an R-algebra A, `contract` pairs
the right factor of A tensor P against an R-linear form P to R. `coefficients`
collects these contractions for every tensor in a given set; `coefficientIdeal`
is their ideal span. The naturality lemmas hold for arbitrary modules.

If P is projective, `eq_zero_iff_contract` proves that all dual contractions
vanish exactly when the tensor is zero. The proof splits P off the free module
on its underlying type, tests the image against each coordinate functional,
and applies the retraction. No finite generation is assumed.

`coefficientIdeal_le_ker_iff` says that an algebra map f from A to any R-algebra
B annihilates the coefficient ideal exactly when every chosen tensor maps to
zero in B tensor P. B need not be flat. `coefficientIdeal_image` proves that
formation of this ideal commutes with arbitrary algebra maps on A. This last
identity does not require projectivity.

These are internal derived constructions and proofs using Mathlib's projective
module splitting, tensor maps, free-module coordinate equivalence, and ideal
span. They do not assert gluing, descent, or closed representability.
