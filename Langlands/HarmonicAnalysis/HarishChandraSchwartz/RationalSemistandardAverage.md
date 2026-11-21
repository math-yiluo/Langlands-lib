# Waldspurger's source average on semistandard spectral families

Waldspurger (2003), VI.3, printed p. 306, sums over the relative Weyl
group and, for each Weyl element, all actual parabolics with its conjugate
Levi. `Average.Pair` is this dependent sum. `Average.scale` is the
reciprocal of `|W^G| |P(M)|`. The pair type is finite by relative Weyl
finiteness and `SemistandardSpectralFiberFinitenessStatement`, with the
parabolic transport from `SemistandardSpectralDynamicCoverageStatement`.
`pairs_card` identifies the count, and the group unit and the nonempty
parabolic fiber make it positive.

`Average.rawAverage` is a complex-linear map on the full product of
actual inducing fibers. Each summand chooses a compact lift and applies
the inverse of the actual normalized V.3 comparison to the coefficient at
the transported inducing object. `target_eq_weylParabolicTarget` identifies
the target with the orbit of the actual Weyl class at the specified parabolic.

For a smooth input, the inverse of the closed V.3 smooth comparison
provides the same inverse on each coefficient. The finite sum of these
smooth components gives `smoothComponent`. The support of the full
average is contained in the literal association saturation of the input;
each summand vanishes outside that saturation. Every class is finite by
the same geometric finiteness premises. These two arguments give the
typed `smoothAverage` on the coherent smooth finite-support family.

Each inverse comparison commutes with the product-group action, so
`rawAverage_action` and `smoothAverage_action` give equivariance.
Invariance of the input makes every summand equal to the input value,
and the reciprocal count then gives `smoothAverage_eq_self`.

`InvariantImageStatement` is the remaining VI.3 pointwise assertion for
this sum on each smooth input. A proof uses the V.3.2 composition law to
reindex the double sum along each comparison arrow.
`LiftIndependenceStatement` specifies equality of the two inverse summands
in the same source fiber when their compact lifts represent the same
Weyl element. It uses inducing covariance and the preceding
`WeylDescent.LiftFiberIndependence` comparison.
The typed `invariantProjector` is conditional on
this image statement. Its evaluation is the same double average, and
the fixed-point law gives its retraction, idempotence on the full
family, and exact range. Its action is the restriction of the
equivariance already proved for the average.
