# Images of rational domains under finite étale affinoid maps

`exists_rationalChart_cover_image` expresses the image of the locus of
any `RationalChart K B` under
`BanachSpectrum.comap f.toBoundedRingHom` as a finite union of rational
loci in \(\mathcal M(A)\). Here `f : BoundedAlgHom K A B` is finite
Banach and algebraically finite étale over a complete ultrametric
normed field, possibly trivially normed. This is the rational-domain
case of the image property in Conrad–Temkin, *Non-archimedean
analytification of algebraic spaces*, Theorem 4.1.2.
[Conrad–Temkin, Theorem 4.1.2](https://math.stanford.edu/~conrad/papers/analgpaper.pdf#page=18)

The proof uses the denominator class of the given chart as \(b_0\)
and the numerator classes as \(b_j\) for \(j>0\). With \(w_0=1\)
and \(w_j\) the reciprocal of the corresponding chart radius, the
chart inequalities say that \(y(b_0)w_0\) is maximal among the
\(y(b_j)w_j\). The classes generate the unit ideal by the rational
presentation hypothesis. `BanachSpectrum.exists_weightedCoeff_iff`
then describes points in the image by maximizers of the weighted
coefficients of the resulting polynomial \(P\).

For every \(d\) in the support of \(P\) with \(d_0>0\), the proof constructs
a rational chart with denominator \(P_d\), numerators \(P_k\) for \(k\)
in the support, and radii \(w^d/w^k\), where \(w^k=\prod_i w_i^{k_i}\).
Surjectivity of the presentation map lifts these classes to the
chosen Tate presentation of \(A\). The coefficients on the support
generate the unit ideal since all other coefficients vanish. The
chart locus is precisely the set where the weighted coefficient
at \(d\) is maximal. At a point of the spectrum such a maximizer
must be in the support, since otherwise every coefficient would
have seminorm zero, contradicting generation of the unit ideal.
Taking the union over these indices recovers the image, allowing an
empty family.

`isOriginalChartDomain_image_rational` transports the equality to
the saturated atlas of `SmallAffinoidSpectrum.saturated A` when
\(\mathcal M(A)\) is `v`-small. Each base rational chart yields a
local domain of the singleton affinoid atlas and hence a chart of
the saturated atlas. The base space is Hausdorff, so
`isOriginalChartDomain_of_finite_chart_cover` recognizes their
union as an original chart domain.
