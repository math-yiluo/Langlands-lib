# Exact arithmetic epsilon data on arbitrary rank-one Weil classes

Worker 1555 derives this internal classification from the constructed
rank-one arithmetic coefficient and full certificate, the actual continuous
character classification of rank-one Weil classes, and the existing
uniqueness theorem for arithmetic epsilon certificates.

`rankOneArithmeticEpsilonData` assigns a complex unit and integer to any two
actual rank-one irreducible Weil quotient classes and any original nontrivial
unitary additive character. The inverse of `rankOneWeilCharacterEquiv` gives
their actual field quasicharacters for the supplied standalone reciprocity.
The coefficient is the constructed Deligne constant of their product at the
proved unique self-dual measure. The exponent is precisely the product's
multiplicative conductor plus the additive conductor.

`rankOneArithmeticEpsilonData_spec` proves that these data satisfy the
complete original arithmetic epsilon certificate. It applies the character
case proved in `RankOneArithmeticEpsilonData`; the inverse laws of the actual
character equivalence identify those character classes with the given
quotient classes. This handles every actual rank-one class and introduces
no extra representative or character-existence premise.

`isArithmeticPairEpsilonFactor_rankOne_iff_eq_data` gives an exact
classification of all coefficients and exponents satisfying that certificate.
Its forward direction compares the supplied certificate with the constructed
one through the published `IsArithmeticPairEpsilonFactor.unique`, then uses
product extensionality. Its reverse direction rewrites the constructed
certificate by equality of the coefficient and exponent. The original
harmonic, Frobenius and restriction existence requirements are proved by the
constructed certificate; the original universal clauses are retained.

`rankOneArithmeticPairEpsilonComparison` compares any two supplied compatible
common-closure reciprocity families and validated local-constant systems on
these actual rank-one classes. Both full certificates are equivalent to the
same constructed coefficient-exponent pair. The standalone reciprocity
candidate is shared explicitly, and each family is assumed compatible with
it. The two systems may have independent carrier universes. No general
uniqueness theorem for common-closure families or nonabelian assignments is
assumed.

Every prime and finite p-adic field is retained. The field universe and
parameter-carrier universe remain independent, as do both system universes.
The result concerns only rank-one arithmetic pair epsilon certificates.
It neither constructs reciprocity or a local-constant system nor proves
analytic JPSS comparison or the closed all-rank supercuspidal correspondence.
