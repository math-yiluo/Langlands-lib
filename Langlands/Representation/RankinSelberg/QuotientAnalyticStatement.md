# Conditional analytic properties of the equal-rank quotient integral

`Langlands.RankinSelberg.EqualRankQuotientAnalyticStatement F T n` is an
internal proposition for every supplied p-adic topological datum and rank
`n + 1`, including rank one. Its two initial premises are the full
`FiniteFunctionMellinStatement` at the field universe and the actual
`QuotientIwasawaIntegrationStatement F T n`. For every pair of smooth
representations, in independent universes, it further assumes the standard
and inverse-character `CoefficientTorusExpansion` propositions.

For each such pair and character there is one nonzero Laurent polynomial
`d`, chosen before the functionals and the compatible quotient measure.
For every pair of functionals, including zero functionals, and every
quotient measure compatible with the published general linear and
unipotent Haar measures, the following hold:

- Each actual equal-rank coefficient-model integral converges absolutely
  on a right half-plane depending on its vectors and Schwartz row test.
- Each such integral has a rational continuation in
  `T.residueCardinality ^ (-s)`, in the existing
  `HasRationalContinuation` sense, including reduced-denominator
  nonvanishing on a right half-plane.
- Every rational continuation `R` in the actual `equalRankRationalValues`
  set satisfies `laurentToRatFunc P = laurentToRatFunc d * R` for some
  Laurent polynomial `P`.

The third clause and `d ≠ 0` give `HasCommonDenominator` for each of those
sets. The stronger order of quantifiers records that the same denominator
works for all functionals, vectors, row tests, and compatible measures.
Right invariance of the unipotent Haar measure remains explicit, as in the
compatibility predicate. All topology and measure structures are those of
the supplied `T`. No irreducibility or nonzero-functional premise is used.

This statement composes three internal interfaces: the compact root
average estimates of `EqualRankRootAverageAnalyticStatement`, continuity
of the actual quotient integrand, and
`QuotientRootIntegrationStatement`. Continuity supplies Borel measurability;
the iterated integral of the norm controls actual quotient integrability.
Only after this convergence is established can the quotient integral be
identified with the iterated root integral. Equality on a right
half-plane then transports rational continuations in both directions,
preserving the root-average denominator.

This file defines the proposition; it supplies no proof. The Mellin and
Iwasawa theorems and the coefficient expansions remain explicit premises.
The statement does not establish the full Whittaker-type expansion
theorem, a unit-value test, or normalized-generator existence, and does
not replace the unconditional `EqualRankAnalyticStatement`. Its
provenance is internal composition of the named interfaces, with no
additional attribution to original literature.
