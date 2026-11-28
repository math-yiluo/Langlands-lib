# Decay of the relative constant-term remainder

`AdelicSiegelMaximalRemainderStatement` assumes the sharp Siegel derivative
bounds for the weighted square-integrable input. It also assumes automorphy
of the ordinary constant term at `J` and at the ambient maximal parabolic
that omits a selected simple root of `J`. For every vector in the split
translation span of the ordinary `J` constant term, its difference with
the ordinary constant term at `J` with that root removed has logarithmic
chamber growth with an extra inverse power of the archimedean root scalar.

The proof applies the maximal-radical remainder estimate to the original
form minus its ambient maximal constant term. The difference has zero
constant term there by idempotence. Differentiation commutes with ordinary
averaging, so the assumed estimates for the original derivatives give the
chamber growth needed for one derivative of the difference. A finite
directional basis gives a single logarithmic degree for that estimate.

Average the resulting bound at `J` and apply the group-algebra operator
that realizes the given orbit vector. The chamber bound survives both
operations. The identity for the composition of ordinary constant terms
identifies the shifted average with the asserted relative remainder,
since the intersection with the ambient maximal parabolic removes the
selected root from `J`.

The one-root gain uses the maximal-parabolic case of the argument in
Delorme's Lemma 3.1, and the change to the relative remainder uses the
composition of ordinary constant terms.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 10–12 and 14, Lemma 3.1, Proposition 3.5 and (3.5)–(3.6).
