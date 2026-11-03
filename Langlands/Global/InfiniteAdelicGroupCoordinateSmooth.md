# Actual infinite adelic coordinate smoothness at the completions

For a number field `F` in any universe, an affine group scheme `G` over `F`,
and any real charted parameter space with model with corners `I`, this
construction compares the existing infinite adelic regular-function criterion
with its criteria on the actual infinite-place completions.

The infinite adelic criterion is exactly `GroupScheme.CoordinateSmooth` with
coefficient ring `InfiniteAdeleRing F` and coefficient map
`InfiniteAdeleRing.ringEquiv_mixedSpace F`. The smooth test space is the existing
finite product of real and complex coordinate spaces, with its normed-space
manifold. It does not use the normalized multiplicative norm on the infinite
adele ring.

`coordinateSmooth_iff_completions` proves that this criterion holds exactly when
the actual point projection at each real place satisfies `CoordinateSmooth`
for its specified completion-to-real ring isomorphism, and the projection at
each complex place satisfies `CoordinateSmooth` for its specified
completion-to-complex ring isomorphism. All these tests evaluate the same
global regular functions on the original group scheme. The independent test
algebra universe allows ordinary real and complex values even when `F` and
its completions are in a larger universe.

The proof first checks real smoothness of a map to the mixed space in its two
product factors, and then componentwise in each finite dependent product.
The actual completion projection evaluation identity identifies the resulting
tests. The reverse argument reassembles these very tests. No manifold instance
on the source is required beyond its stated charted-space structure.

`coordinateSmoothCompletionFamilyEquiv` packages the existing point completion
homeomorphism into an equivalence of the indicated subtypes of parameter
families. It uses projection and assembly on the original point carrier and
the preceding criterion in both directions; the inverse identities are the
actual completion decomposition identities.

`coordinateSmooth_continuous` additionally proves that every mixed-coordinate
smooth family is continuous into the original infinite adelic evaluation
topology, without affineness. For each regular function its mixed-coordinate
value is continuous by smoothness. Composing with the existing continuous
inverse mixed-coordinate homeomorphism gives continuity of its actual
infinite adelic value. The defining evaluation topology then gives continuity
of the point family.

This is internal derived infrastructure using the existing coefficient product
and evaluation identities, mixed-coordinate homeomorphism and Mathlib's finite
product smoothness criteria. No smoothness or reductivity of `G` is assumed.
It does not assert an analytic manifold or Lie group structure on `G(F∞)`,
identify the local tests with the manifold of a base-changed group, or prove
any differential growth, measure or reduction result.
