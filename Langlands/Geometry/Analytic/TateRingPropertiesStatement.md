# Ring properties of actual strict Tate algebras

Author: Worker 56.

`StrictTateAlgebra.TateRingPropertiesStatement K` states that, for every
finite number of variables, the actual strict Tate algebra over the
complete ultrametric normed field `K` is Noetherian, is a domain, has
unique factorization, and is integrally closed in its fraction ring.
These are Mathlib's ordinary ring properties applied to the constructed
restricted-series algebra. They are conclusions of the proposition,
not assumptions on the algebra. The coefficient valuation may be trivial.

The source is Proposition 2.3.2(i),(iii), pages 5–6, and Corollary 2.3.3,
page 6, of the retained fourteen-page notes of part of Vladimir
Berkovich's course, “2. Affinoid algebras.” They give Noetherianity and
factoriality of the finite-variable Tate algebra. The source's
factoriality includes the domain property, made explicit here.

Integral closedness is the standard algebraic consequence of unique
factorization. Its use for the Tate algebra also appears in the source's
proof of Proposition 2.6.1, domain case, page 11. The Lean implementation
derives it through Mathlib's integrally-closed result for unique
factorization domains. Grouping these properties into one proposition is
an internal choice for reviewing the common proof infrastructure. The
Jacobson conclusion of Corollary 2.3.3 is outside this target.

Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The note-taker and publication date are unidentified.
