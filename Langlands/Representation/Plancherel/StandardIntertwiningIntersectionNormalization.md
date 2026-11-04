# Compact-open normalization of the intermediate intersection chart

This derived construction transports actual subgroup measures through canonical
continuous group equivalences. It applies the local volume construction of
`CompactOpenFactorProduct` to the restricted chart of
`StandardIntertwiningIntersectionFactorization`. It is motivated by Waldspurger
(2003), IV.1, printed p.279 (PDF p.45) and IV.1(12), printed p.283 (PDF p.49).
Actual reductive existence of the three original charts, prescribed source Haar
comparisons, convergence and analytic continuation remain application obligations.

Write I20 = U0 subgroupOf U2 and I21 = U1 subgroupOf U2. The two actual subgroups
of I21 are H = I20 subgroupOf I21 and K = (V subgroupOf U2) subgroupOf I21.
The three original charts imply I20 lies in I21. `intersectionKernelEquiv`
therefore identifies H with I20. `intersectionComplementEquiv` identifies K with
V using the two supplied inclusions of V. Neither operation restricts an ambient
Haar measure. `intersectionSubgroupProduct` applies these identifications to
`intersectionFirst`, and its value is actual multiplication in I21.

Given measures on I21, H and K and compact-open subgroups S of I21 and B of K,
`intersectionKernelMeasure` pushes the independent H measure to I20.
`intersectionNormalizedFactor` scales the K measure by the explicit scalar
from `compactOpenFactorScalar`, then pushes it to V. This scalar is ambient S
volume divided by the product of the H-intersection and K-B volumes. It does
not depend on a chosen quotient measure. The kernel transport preserves Haar,
regularity and S-finiteness; the factor transport preserves regularity and
S-finiteness and is Haar when the displayed compactness and closedness premises
hold.

For `measurePreserving_intersectionFirst_of_localProduct`, the middle intersection
is locally compact and the ambient group is Hausdorff and topological. All five
individual measurable structures are Borel, and the product measurable structures
on H times K and I20 times V are their Borel structures. The middle-intersection measure is regular Haar and the H and K
measures are regular two-sided Haar and S-finite. Their product is regular.
A compatible Weil measure on the actual H quotient of I21 remains explicit,
as do closedness of H and compactness of S and B. The only local geometric
premise states that literal multiplication sends (H intersect S) times B onto S.
The proof first derives exact product normalization for the constructed K
measure. It then uses the pushforward formula for product measures and composition
to obtain exact measure preservation of `intersectionFirst` in the original
I20 and V carriers. No product-measure identity is an input to this theorem.
