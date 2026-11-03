# Characters of a quotient by one integral relation

This internal algebraic construction supports the scheme-kernel and weight
comparison in the proof of the relative-root kernel centralizer theorem.
It implements the ordinary universal property of the quotient abelian group
`Λ/ℤa`; the relation is not saturated.

`quotientCharactersEquiv` identifies multiplicative characters of that quotient
with characters of `Λ` killing `a`. Its inverse is the quotient lift of the
associated additive homomorphism. `quotientUniversalCharacter` is the monomial
character with values in the units of the quotient group algebra.
`quotientUniversalCharacter_eq_one_iff` proves that this character evaluates
to one at `b` precisely when `b ∈ ℤa`, by comparing the distinct monomials at
`[b]` and zero. The coefficient ring is any nontrivial commutative ring.

This argument retains torsion in the quotient, including torsion divisible by
the characteristic of a coefficient field. No reducedness or smoothness claim
is made.
