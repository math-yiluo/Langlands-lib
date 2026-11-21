# Reduction of the regular elliptic case to rational comparison

`FundamentalLemmaGlobalizationReductionStatement` gives the regular elliptic
fundamental lemma for the p-adic fields, spherical functions, base-change
homomorphisms and mass-one Haar measures of the Library target. It takes the
cyclic field globalization, existence of regular orbital profiles,
`RationalSphericalConcordanceNearEllipticStatement`, the elliptic norm
criterion, and existence of Satake characters over both fields as hypotheses.

The rational comparison hypothesis starts with a cyclic extension of number
fields giving the local fields and intertwining the twists at the
distinguished place. All infinite places split. There are arbitrarily large
finite split and inert places outside any finite set. For each regular elliptic
associated pair at the distinguished place, it supplies a finite set of
places containing that place, regular associated pairs there, and
neighborhoods of those pairs. The distinguished pair is the specified one.
Rational associated pairs with regular base element meeting all these
neighborhoods must satisfy `ConcordAt` for the transported pair at the
distinguished place and the original spherical tests.

To prove the associated branch, globalize the cyclic extension and pull the
given pair back through the coefficient isomorphisms. The rational
approximation theorem preserves the prescribed neighborhoods and the value
of the locally constant concordance predicate at the original associated
pair. Applying rational comparison to the resulting rational pair therefore
gives equality of the original orbital integrals for all compatible associated
measures. For the off-norm branch, the elliptic norm criterion and the two
Satake character statements give the determinant-support reduction.

This internal reduction isolates the globalization and density steps in
Arthur–Clozel (1989), Chapter 1, proof of Theorem 4.5, pp. 42–46, and
Henniart–Lemaire (2011), I.6.8, pp. 49–50. It leaves the construction of the
auxiliary tests and the rational trace comparison as explicit premises.
