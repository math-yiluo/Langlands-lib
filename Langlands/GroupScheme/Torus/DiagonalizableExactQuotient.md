# Exact quotients of diagonalizable groups

This internal construction supplies an explicit quotient used in the canonical
factorization of homomorphisms from groups of multiplicative type. Its
provenance is derived from the Library's diagonalizable group functor,
restriction of characters, and faithful flatness for injective character maps.
The construction does not assert the existence of quotients for arbitrary
subgroups or nonsplit groups.

For an additive homomorphism `p : Λ →+ Γ` of abelian groups, the definition
`exactQuotientMap R p` is restriction of characters along `(ker p) ↪ Λ`.
It has source `D_R(Λ)` and target `D_R(ker p)`.

If `p` is surjective, `kernel_exactQuotientMap` identifies the full kernel
subgroup functor with the range of the induced map `D_R(Γ) → D_R(Λ)`.
This equality is proved on every test scheme. A character of `Λ` in the kernel
kills `ker p`; its additive version factors through `Λ / ker p`, and the first
isomorphism theorem identifies that quotient with `Γ`. Conversely a character
pulled back from `Γ` kills `ker p`. All torsion is retained.

If `R` is nonzero and Noetherian and `Λ` is finitely generated,
`isFppfQuotient_exactQuotientMap` proves the represented fppf quotient
predicate of the Library. The character subgroup inclusion is injective, so
the existing diagonalizable faithful flatness theorem gives flatness and
surjectivity. Both character groups are finitely generated, and the target
is locally Noetherian. Finite type of the source over the base then gives
local finite presentation of the quotient map.
