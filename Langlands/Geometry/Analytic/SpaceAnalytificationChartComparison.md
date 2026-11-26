# A covering family presents its analytification as an analytic quotient

Let \(X\) be a separated algebraic space over a complete nontrivially
valued ultrametric field \(K\). Suppose \((Y,p)\) satisfies
`SpaceAnalytification.IsAnalytification`, and let `ChartData X` be a family
of étale affine charts covering the affine test points of \(X\).

`IsAnalytification.chartQuotient` constructs the quotient presentation
`QuotientData` on \(Y\) using the maps that \(p\) assigns to the charts.
Those maps are étale. Given a point of \(Y\), joint surjectivity of the
étale tests first lifts it to one such test. The chosen charts cover the
test on prime spectra. `exists_mem_range_localizedHom` lifts the analytic
point of that test to the analytification of one of its intersections
with the chosen charts. The analytified pullback square maps the lift to
the chosen chart over the original point of \(Y\). For each pair of
chosen charts, the analytification of their actual affine fibre product
is the fibre product of their analytic maps to \(Y\).

`IsAnalytification.existsUnique_desc_chartQuotient` gives the comparison
with descent of maps to an analytic target \(T\) whose Hom presheaf on
the étale site of \(Y\) is a sheaf. Two lifts to the charts with the same
composite to \(Y\) factor through the analytified intersection, so agreement
on those intersections implies agreement on all overlaps. The étale
sheaf condition then gives a unique map from \(Y\) to \(T\).

This is the componentwise quotient of the analytified étale relation
in Conrad–Temkin, *Non-archimedean analytification of algebraic spaces*,
Definition 4.1.1 and the sheaf comparison on pp. 18–19. The registered
source is `conrad-temkin-2009-nonarchimedean-analytification`, SHA-256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Separatedness of \(X\) gives affine finite-type intersections of the
chosen charts. This comparison takes an analytification as input and
recovers its quotient presentation for any choice of covering family.
