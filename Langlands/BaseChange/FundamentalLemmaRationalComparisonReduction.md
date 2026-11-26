# The spherical fundamental lemma from rational comparison and the elliptic norm criterion

`FundamentalLemmaRationalComparisonReductionStatement.{u,v}` gives the
full `FundamentalLemmaStatement.{u,v}` from two propositions.

- `Langlands.TraceFormula.RationalSphericalConcordanceNearEllipticStatement.{u,v}`
  gives concordance at rational associated pairs satisfying finitely many
  open auxiliary conditions near a given regular elliptic norm pair.
- `Langlands.BaseChange.EllipticNormCriterionStatement.{u,v}` identifies
  regular elliptic matrix norms by the scalar norm condition on the
  determinant.

The theorem `fundamentalLemmaRationalComparisonReduction` applies
`fundamentalLemmaGlobalizationReduction` with cyclic field globalization,
existence of regular orbital profiles, and existence of Satake characters
on both fields. Rational approximation and local constancy give matching
at each regular elliptic associated pair. The determinant support theorem
and the elliptic norm criterion give vanishing on the regular elliptic
non-norms. Finally `fundamentalLemmaEllipticReduction` uses the existence
of the smaller-rank base-change homomorphisms and parabolic descent to
give concordance on the full regular semisimple locus.

The reduction assembles the elliptic globalization and parabolic descent
steps of Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced
Theory of the Trace Formula* (1989), Chapter 1, Theorem 4.5, printed
pp. 39–47, and Henniart–Lemaire, *Changement de base et induction automorphe
pour GLₙ en caractéristique non nulle* (2011), I.6.6–I.6.12, printed
pp. 47–53.

- Arthur–Clozel source ID `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
- Henniart–Lemaire source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
  SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
