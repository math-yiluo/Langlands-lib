# Actual rational and norm-one adelic homogeneous quotients

For an actual group scheme `G` over an arbitrary number field `F`,
`RationalQuotient F G` is the left homogeneous quotient of the actual adelic
point group by the image of its actual principal rational map.
`NormOneRationalQuotient F G` is the corresponding left homogeneous quotient
inside the previously constructed norm-one subgroup. Both reuse
`LeftCosetSpace`, so representatives differ by left multiplication and right
translation sends `[x]` to `[x * g]`. No normality of the rational subgroup is
assumed, and no quotient group structure is asserted.

The actual norm-one subgroup inclusion descends to
`normOneQuotientInclusion`. Its injectivity follows because a rational relation
between two norm-one points already gives a rational relation inside the
norm-one subgroup: every principal rational point is norm one by the published
product formula. The quotient universal property proves continuity. The
inverse image of its range under the full quotient projection is exactly the
norm-one subgroup. More generally, inverse images of images of subsets are
the images under subgroup inclusion of their norm-one quotient inverse
images. Since the norm-one subgroup is closed, this identity proves that the
descended inclusion is a closed map and hence a closed embedding. The map
intertwines positive right translation by actual norm-one elements.

`rationalQuotientFunctionEquiv` identifies arbitrary quotient functions with
actual adelic functions invariant under every principal rational point. Its
inverse is quotient descent; its two inverse identities are proved. Pullback
carries positive right translation to the formula `f(x * g)` on invariant
functions. The coefficient type can be in an independent universe. This is a
function equivalence, without extra analytic or growth conditions.

When `G` is affine and its structure morphism is locally of finite type, the
previously proved rational closedness and actual adelic local compactness give
Hausdorff and locally compact structures on both homogeneous quotients. All
topologies are the actual quotient topologies, and the positive right actions
and open quotient projections are those of the reused generic quotient API.

The original arithmetic quotient conventions are Getz–Hahn, *An Introduction
to Automorphic Representations* (2024), Section 2.6, printed pages 67–69:
the opening rational quotient, the norm-one subgroup (2.19), and the domain
of (2.22). The present unit's closed-embedding comparison is an internal
consequence of these actual subgroups and the quotient universal property.
It does not construct the split-centre subgroup `A_G` of (2.20), the
split-centre quotient `[G]` of (2.21), or the homeomorphism in (2.22).
Polishness, invariant quotient measures, Weil compatibility, finite volume,
reduction theory and automorphic analytic conditions remain separate
obligations. No second-countability or finite-volume conclusion is used here.
