# Proof of anisotropic toral reduction for quadratic cocycles

`Langlands.GroupScheme.numberFieldQuadraticQuasiSplitToralReduction`
proves `NumberFieldQuadraticQuasiSplitToralReductionStatement.{u}`
with its given hypotheses.

Use `exists_quadraticOppositeBorelTorus` to choose a Borel over the
quadratic field whose intersection with its Galois translate descends
to a maximal torus over the number field. Then
`IsQuadraticOppositeBorelTorus.split_anisotropic` applies the rigidity
hypothesis to the torus's geometric character action. Its base
change to the quadratic field is split and its split rank over the
number field is zero.

The theorem `IsQuadraticOppositeBorelTorus.exists_realLocallyTrivialRepresentative`
produces a torus cocycle on the same cover from the open cell of
the Borel pair. Weak approximation imposes local triviality at
real places with a complex place above them. At a real place with
a real place above it, the pullback cover has a section and the
torus cocycle is trivial there. Symmetry of `Cohomologous` gives
the comparison in the direction of the statement.

The Borel pair and the real-place argument follow V. Platonov and
A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), Lemmas
6.17 and 6.28, printed pp. 329–330 and 369–370. The sign computation
uses Lemma 6.18, printed p. 330. The registered source is
`platonov-rapinchuk-1994-algebraic-groups-number-theory` with SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`.
