# Actual root-map isomorphisms at equal zero-fixer depths

This internal supporting module concerns two characterized smooth neutral
zero-fixer models over the actual maximal unramified integers of a
nonarchimedean local field, in arbitrary universe `u`. The models are supplied
with a compatible morphism `φ` and an integral split torus `T` in its source.
The target integral torus is exactly `φ.mapIntegralTorus T`.

Both apartment subsets are nonempty and bounded above under every real affine
functional. Their neutral integral-point images are assumed to equal the
specified unramified zero subgroup intersected with their pointwise fixers.
For an actual relative root `a` and a common apartment reference point `x`,
equality of the two actual `rootFixerDepth` values makes
`φ.integralRootMap T hT a a.2.1` an isomorphism. The theorem requires no
smoothness of the ambient map `φ`, no facet hypothesis, and no inclusion
between the two subsets.

The proof forms the actual source and target root-filtration model data using
`unramifiedZeroRootFiltrationModelData`. Equality of depths gives equality
of their specified filtration subgroups. The imported
`unramifiedModelIsoOfFiltrationEq` then gives a compatible isomorphism
between these actual models, using the published smooth homomorphism extension
theorem over the maximal unramified integers. Generic rigidity and the
generic inclusion squares show that its underlying map has the same ambient
factorization as `φ.integralRootMap`. Cancellation through the full represented
target root inclusion identifies the two integral maps.

The residue statement applies actual residue base change to this isomorphism.
It therefore concerns the existing `φ.residueRootMap`, with its exact integral
origin and all-test factorization, rather than a separately chosen map on
residue-field points. `integralRootIsoOfRootFixerDepthEq` packages the integral
isomorphism with forward map definitionally equal to the canonical root map;
the final simplification theorem records that equality.

These are internal deductions from the imported model comparison, zero-fixer
root-model, and canonical root-map constructions. They do not prove the
strict-depth branch, the sign/depth relation for incident facets, smoothness
of the full incident model kernel, or the host common-torus Lie-weight formula.
