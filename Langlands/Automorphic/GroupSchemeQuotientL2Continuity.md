# Joint continuity of the actual canonical quotient L2 right action

This internal construction bundles the existing canonical
`quotientL2RightAction` as a continuous map of the adelic group element
and the actual quotient L2 vector. It uses exactly
`positiveRationalQuotientHaarMeasure` on the existing positive-central
rational quotient, with its original norm-one normalization. Its
evaluation formula is the unchanged action. Restricting to a fixed
vector gives `haarQuotientL2OrbitMap`.

The hypotheses retain an arbitrary number field, an actual affine
group scheme locally of finite type, a supplied central split torus
map, injective finite-index character restriction, its finite splitting
and right invariance of the fixed norm-one Haar measure. Reductivity
and finite covolume are not needed for this continuity construction.
No claim that the supplied torus is the greatest rational split
center is made.

The implemented argument uses the established Hausdorff and Borel
structures on the positive quotient and regularity of its canonical
measure. These supply the separation, compact inner regularity and
local finiteness required by pinned Mathlib's
`Continuous.compMeasurePreservingLp`. The original quotient right
translation is jointly continuous by its existing continuous opposite
group action. Currying that continuous map produces a continuous
family of continuous quotient maps. The existing exact right-invariance
theorem makes every such map measure preserving.

Mathlib's joint continuity of measure-preserving composition in
`Lp`, specialized to exponent two, now gives the continuous map.
This operation is precisely the original positive right pullback
used in `quotientL2RightAction`. The construction operates on actual
null classes and does not assert a pointwise identity for their
chosen representatives.

Provenance is internal: this is a direct adapter between the existing
actual quotient topology, canonical measure and L2 action in
`GroupSchemeQuotientL2` and the pinned Mathlib continuity theorem in
`MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving`.
No new literature theorem is attributed to it. It asserts neither
cuspidal density, finite volume, smooth-vector realization, spectral
decomposition nor trace-class properties.
