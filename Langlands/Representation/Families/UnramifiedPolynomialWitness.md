# Polynomial witnesses for nonvanishing of unramified regular functions

Worker 1444, with Worker 1664's published monomial-clearing proof adapted
as described below. This is an internal construction for the coordinate
step in Renard VI.8.4.

`polynomialToLaurent` includes ordinary complex polynomials in the additive
group algebra of integer exponent vectors. It sends a monomial with
nonnegative exponent vector to the same formal Laurent monomial.
`polynomialToLaurent_eval` identifies its evaluation with the existing
`Plancherel.finiteLaurentEvaluation`.

`exists_monomial_clearing` proves that multiplying any finite Laurent
polynomial by one nonnegative monomial produces an ordinary polynomial.
Its proof is adapted from the local `hclear` argument in Worker 1664's
published `Plancherel.finiteLaurent_exists_zero_eval_ne_zero`, in
`Langlands/Representation/Plancherel/RationalUnramifiedLocalDivisibilityProof.lean`.
It treats zero, sums and individual monomials. A sum is cleared with the
sum of its two clearing exponent vectors; an individual integer exponent
is separated into its positive and negative parts. This extraction does
not alter the published proof or import its local divisibility theorem.

`clearingExponent` and `polynomialNumerator` choose witnesses of this
existence statement. Their exact clearing identity is proved. Evaluation
of the clearing monomial is a product of units at every torus point.
Consequently the numerator has exactly the same nonvanishing locus as
the original Laurent polynomial. The construction includes rank zero
and the zero polynomial.

For a connected reductive group over an arbitrary nonarchimedean local
field, `rationalRegularPolynomial` applies this construction to the
preimage of an actual regular function under the published canonical
Laurent-algebra equivalence. The rational point group has its canonical
topology. Connected reductivity supplies affineness and local finite
type. These two properties are exposed as typeclass arguments, as in the
imported canonical Laurent comparison: `hG.isAffineHom` gives affineness,
and `hG.smooth` gives local finite type. Thus they impose no restriction
on the connected reductive group. There is no extra continuity,
characteristic, splitness or rank premise.

`canonicalLaurent_eval` specializes the existing evaluation comparison
to the canonical topology and coordinates.
`rationalRegularPolynomial_eval_ne_zero_iff` therefore identifies
nonvanishing at every actual unramified character.
`principalOpen_rationalRegularPolynomial` proves equality with the
published `Plancherel.rationalUnramifiedPrincipalOpen`, in exactly the
polynomial ring used by `InducedIrreducibilityOpenStatement`.

The provenance is the published coordinate-algebra and evaluation
comparisons, Worker 1664's exponent-clearing argument and elementary
commutative algebra. The intended use is to convert a regular determinant
witness from Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 version, VI.8.4 Proposition proof, printed pp.192–193 /
PDF pp.198–199, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
No representation-theoretic assertion is made: this construction supplies
no compact subgroup, finite fixed-vector model or detector of
irreducible subquotients.
