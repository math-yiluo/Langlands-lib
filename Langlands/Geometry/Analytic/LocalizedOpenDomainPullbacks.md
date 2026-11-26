# Pullbacks by open analytic domains

`OpenPullbackChart` describes actual localized morphisms of analytic domains forming a pullback. It identifies the domain in the proposed pullback by its two projections. Only the two outside domains need open carriers.

Start with a commuting square over a complete ultrametric normed field and a family of Cartesian domain charts. For every pair of points in the two outside spaces with equal images in the base, require a chart whose left domain contains the first point and whose right domain contains the second. For a compatible test cone, take the intersection of the two inverse images for each chart. These intersections are open and cover the test space by the point-pair hypothesis.

`openDomainChartPullbackIsLimit` constructs the limiting pullback cone. Over each intersection the two test morphisms factor through the outside domains, giving a unique lift to the chart's pullback domain. The lifts agree on overlaps and glue by localized morphism descent. `isPullback_of_openDomainCharts` gives the resulting Cartesian square.

This criterion derives from the unique factorization property of analytic domains in Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990), §3.1, p. 48. The proof of Theorem 3.4.1, steps (2)–(3), pp. 63–64, uses inverse-image open domains and affine-open gluing to construct scheme analytification.
