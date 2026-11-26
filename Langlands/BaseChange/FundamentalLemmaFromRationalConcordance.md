# The spherical fundamental lemma from rational spherical concordance

`FundamentalLemmaFromRationalConcordanceStatement.{u,v}` gives
`FundamentalLemmaStatement.{u,v}` from
`Langlands.TraceFormula.RationalSphericalConcordanceNearEllipticStatement.{u,v}`.
The premise is the orbital comparison at rational associated pairs near a
regular elliptic norm pair that satisfy finitely many auxiliary open conditions.

The Lean proof applies `fundamentalLemmaRationalComparisonReduction` to the
rational comparison and `ellipticNormCriterion`. The reduction uses rational
approximation and local constancy at regular elliptic norms. At regular
elliptic non-norms, the norm criterion and determinant support yield the
vanishing of the ordinary orbital integral. Parabolic descent then gives
concordance on the full regular semisimple locus.

This assembly uses the rational approximation and descent steps of
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), Chapter 1, §4, printed pp. 39–47. The elliptic
determinant norm criterion comes from Chapter 1, Lemma 1.4, printed pp. 8–9,
and Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ
en caractéristique non nulle* (2011), I.6.12, printed p. 53.
