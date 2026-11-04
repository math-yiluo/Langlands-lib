# Scalar extension of actual subgroup tangent images

This internal construction works over any field extension `k → K`, in an
arbitrary common universe. The ambient group and the supplied representative
are affine and locally of finite type over `k`.

`extendedLieSubmodule G W` is the `K`-linear span of the images of vectors of
`W` under `x ↦ Lie.schemeScalarExtension G (1 ⊗ x)`. The target is the actual
dual-number identity kernel of the scheme pullback, not an abstract replacement
for its Lie algebra. The construction is monotone and commutes with arbitrary
suprema, including an empty supremum. The supremum proof uses submodule-sum
induction on each original vector, followed by scalar-span closure.

`Lie.targetMapLinear_schemeScalarExtension_one_tmul` identifies the two ways
to extend a vector and apply the differential of a group homomorphism. It follows
from the existing compatibility of actual kernel coefficient extension with
postcomposition and the pure-vector formula for `schemeScalarExtension`.

`range_targetMapLinear_baseChange` identifies the range of the pulled-back
differential with the extended span of its original range. For one inclusion,
the surjective tensor comparison and tensor induction reduce to pure tensors;
the compatibility just described and linearity put their images in the span.
For the other inclusion, every spanning generator lifts through the differential
of the pulled-back homomorphism.

`tangentSubmodule_baseChange` applies this range comparison to an all-test
subgroup represented by a monomorphic homomorphism. Monicity identifies the
intrinsic tangent image with the differential range, both before and after
pullback. `HasLieImage.baseChange` then transports any specified exact Lie image.
Neither smoothness nor connectedness of the representative is required.

The provenance is internal: these results combine the published actual
kernel coefficient-extension comparison, tensor scalar-extension equivalence,
differential-range description of represented tangent images, and preservation
of representatives under base change. They are supporting results for the
semigroup subgroup comparison; they do not themselves identify those subgroup
functors or prove the ordered semigroup product theorem.
