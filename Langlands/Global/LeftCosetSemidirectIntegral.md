# Normalized periods for split lattices in semidirect products

`normalizedFundamentalDomainIntegral` integrates a complex-valued function
against Haar measure on the chosen lattice fundamental domain and divides by
the Haar mass of that domain when the mass is positive and finite.

`Semidirect.normalizedFundamentalDomainIntegral_eq_iterated` applies to a
semidirect product with split discrete subgroups and three compact quotients.
For a continuous function invariant under the full lattice, integrating with
the normalized Haar measure on the full domain is the same as integrating first
over the normal domain and then over the complement domain, both normalized.

The proof uses the product fundamental domain and the Haar comparison already
proved in `LeftCosetSemidirectPeriod` and `LeftCosetSemidirectFiniteVolume`.
Boundedness on the compact full quotient gives integrability on the product
domain for Fubini's theorem. The scalar in the Haar comparison cancels against
the same scalar in the mass of the product domain.

This is a derived integration lemma for the nested unipotent constant terms
used in Langlands's proof of Proposition 2, printed pp. 204–205 (Corvallis Part I,
PDF pp. 199–200), from the constant term in Lemma 4 to the cuspidal
Levi functions in conditions (a)–(b). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
