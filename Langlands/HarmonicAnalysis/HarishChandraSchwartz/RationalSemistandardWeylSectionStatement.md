# Actual Weyl comparison of smooth intrinsic semistandard sections

`ClosedSectionComparisonStatement` specifies the normalized comparison of
Waldspurger V.3 and VI.3 on the intrinsic semistandard orbit sections of
`RationalSemistandardOrbitSections`. `HasIntrinsicSourceNormalization` fixes the special-point compact
in the compatible apartment of the very maximal split torus indexing the
semistandard parabolics. All original standard integrals, the compact
probability and the section levels use this compact. The inducing discrete
series uses the absolute Weil scale on its actual split-central quotient.
`normalizationAt` keeps this quotient and Haar measure at every actual
inducing representative. `IsActualFamily` requires these normalization data
and a particular translated V.3 comparison at each representative. The
comparison certificate retains the Haar pushforward and source scale on
both sides, with the actual continuation and
germ specification, at that representative. The value is `comparisonAtOne`
in the two intrinsic product-induced coefficient fibers. The private
`unitaryFamilyOfComparison` checks that the certified family has the same
type as the family used by the pointwise adapter. The regularity and
preservation assertions are part of the witness for the actual tensor.

`InducingNaturality` compares every pair of isomorphic inducing objects in
that orbit. It transports the displayed equivalence by the same inverse
Levi conjugation that defines the target inducing object. Its two sides
use the published pointwise product coefficient transport, including the
actual smooth dual. This includes parameter representatives related by
a self-twist.

`Realizes` specifies the whole section comparison at the actual conjugate
representatives. Its linear equivalence acts on the two intrinsic smooth
coherent orbit section spaces. `Level`, `ofLevel` and `refineLevel` are the
corresponding specializations of the existing `OrbitSectionLevel` and its
inclusions. `RespectsLevels` requires actual level equivalences, the two
inclusion squares, and compatibility with every displayed refinement.
These levels use the fixed vectors of the actual H × H action on the
same smooth orbit sections. `exists_ofLevel` specializes the published
cofinality of these compact levels to the intrinsic smooth sections.
The statement concludes existence and
presentation independence, with all continuation data in its conclusions.

The source locators are Waldspurger, *La formule de Plancherel pour les
groupes p-adiques* (2003), I.1 printed pp. 238 and 240/PDF pp. 4 and 6,
III.1 (3) printed p. 265/PDF p. 31, V.2 printed p. 293/PDF p. 59,
V.3 printed p. 295/PDF p. 61, VI.1 printed pp. 295–296/PDF pp. 61–62,
and VI.3 printed pp. 301 and 306/PDF pp. 67 and 72.
