# Centered Speh induction and tempered Langlands data

Author: Worker 1745.

This is an internal adapter derived from the published definitions in
`TadicUnitaryStatement` and `LanglandsData`, the published square-integrable
to tempered implication in `LeviDiscreteSeriesTemperedProof`, and the actual
head-kernel comparisons in `CanonicalConstituents`. It introduces no
classification premise or quotient existence field.

For `d : SpehDatum.{uF,uV} F T`, `d.degree_pos` records positivity of
`d.length * d.rank`, and `d.exponent_strictAnti` proves that the real numbers
`(length - 1)/2 - i` decrease strictly with `i`. The proof uses the strict
increase of the natural index under its real cast.

Given `hd : d.IsDiscreteSeries`, `d.temperedLanglandsDatum hd` has exactly
the uniform shape of the centered induction, the constant block family
`d.delta`, and exactly `d.exponent`. Irreducibility is supplied by `hd`.
For every Borel Haar measure of the actual central quotient, the published
theorem `isTemperedModCenter_of_squareIntegrable` turns `hd`'s square
integrability into temperedness. Thus the construction retains the original
analytic predicate, normalization, block order, field universe `uF`, and
independent representation universe `uV`.

Its standard module is definitionally `d.centeredInduced`; this is proved by
`temperedLanglandsDatum_standardModule`. Consequently its Langlands quotient
relation is exactly `IsIrreducibleQuotient` for that centered induction,
as recorded by `isLanglandsQuotient_iff`.

Finally, `isSpeh_of_isLanglandsHead` converts an actual strong irreducible
Langlands head into `d.IsSpeh`. The head supplies an irreducible surjective
quotient map. Every other irreducible quotient map has the same kernel, so
both targets are isomorphic to the quotient by the head kernel and hence to
each other. This proves precisely the isomorphism-class uniqueness required
by `IsSpeh`. It does not assert that an arbitrary datum has a head, that Speh
representations are unitarizable, or that the unitary dual is exhausted.

The Speh and Langlands conventions are those of the imported published
pairs. No additional original-source assertion is introduced by this
adapter.
