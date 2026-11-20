# Local rank-one index reduction to E6 and D4

`LocalRankOneTitsIndexReductionToE6D4Statement` uses the hypotheses of
`LocalRankOneTitsIndexStatement`. It gives one of the five index alternatives,
the E6 branch marking with trivial full star action, or the D4 central
marking with trivial full star action or no leaf fixed by the full star action.
The index predicates retain the actual Cartan entries and distinguished
vertices over every nonarchimedean local field.

The proof `localRankOneTitsIndexReductionToE6D4` applies
`localRankOneTitsIndexReduction`. For its higher-B case it applies
`TitsIndexData.not_hasRankOneHigherBIndex_of_oddQuadraticPresentation`
with `typeBOddQuadraticPresentation`. The latter supplies the actual
odd-dimensional radical-free quadratic form and central isogeny, with the
characteristic-two polar radical accounted for. The local Witt-index bound
in the exclusion gives split rank at least two for the higher-B candidate.
The other disjuncts of the preceding reduction give the conclusion directly.

The statement and proof are an internal composition of the preceding
index reduction, type-B presentation and local quadratic exclusion.
