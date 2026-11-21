# Taylor coefficient pole detection on a complex line

`AnalyticallyDividesAt den num z` means that `num` agrees near `z` with `den` times
a scalar function analytic at `z`. On a complex line, `analyticallyDividesAt_of_order_le`
proves this divisibility for analytic germs when `den` has finite order and `num`
has at least that order. Both germs are factored by the centered coordinate raised
to the order of `den`. The remaining factor of `den` is invertible near `z`.

`analyticallyDividesAt_of_automorphic_tests` takes a weakly holomorphic curve in a
uniform-growth stage. The curve is automorphic on a nonempty open subset of its
connected holomorphy domain, and a family of continuous scalar tests separates
zero from the other automorphic vectors. At a point of the domain, let `den` be
a nonzero analytic germ that divides all the tested germs. The theorem proves
that `den` divides the germ obtained from any continuous scalar test.

Write `m` for the analytic order of `den`. Additivity of order under multiplication
shows that each tested function has all derivatives of order below `m` equal to
zero. The growth-space Taylor coefficient theorem realizes these derivatives, divided
by their factorials, as scalar tests of actual automorphic vectors. Separation makes
each vector of order below `m` zero. Consequently every continuous scalar
evaluation has order at least `m`, so the scalar division lemma applies.

The line argument is derived for the pole-detection step in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §8.6, pp. 225–226.
It uses the general number-field theorem in `GroupSchemeUniformGrowthAutomorphicTaylor`
to obtain automorphy of the Taylor vectors. The separation and analytic test
divisibility are explicit hypotheses. The conclusion concerns scalar germs on a
complex line.
