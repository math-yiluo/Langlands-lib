# The actual Galois action on an extended original integral image

Let `F` be an arbitrary nonarchimedean local field and `L/F` an arbitrary
algebraic field extension, in the same arbitrary universe. The extension
may have infinite degree. Let `M` be the supplied integral model over the
actual valuation integers of `F`.

`baseChangeSpectral` is the actual coefficient base change of `M` to the
integer ring of the existing spectral valuation on `L`. The proof first
shows that this valuation extends the original canonical valuation,
using the existing local norm and its comparison with the valuative
relation. The resulting integer-ring map is the restriction of the
given field inclusion.

The spectral norm is unchanged by every `F`-algebra automorphism of `L`.
Consequently `spectralIntegerRange_conjugate_iff` proves preservation
and reflection of the actual integer-ring range. Applying
`baseChangeIntegralPointAut` constructs `spectralIntegralPointAction`,
an actual homomorphism from the full coefficient automorphism group
to multiplicative automorphisms of the extended original integral
image. Its coercion is exactly the existing `rationalConjugate`.
The homomorphism laws follow from the existing ambient conjugation laws.
No separate ring-preservation premise occurs.

The spectral valuation also gives the required scalar intersection:
an element of `F` lies in the extended integer ring exactly when it
lies in its original integer ring. The published integral-image
descent theorem then proves preservation and reflection of
`M.integralPoints` under the existing `rationalExtend`.

`spectralIntegralFixedSubgroup` is the subgroup fixed by this constructed
action on the extended original integral image.
`spectralIntegralFixedCoefficient` sends it to the existing fixed
coefficient-point subgroup, by the exact conjugation comparison.
`spectralIntegralFixedExtend` restricts the existing rational extension
to a homomorphism from the original integral image into this fixed subgroup.

If `L/F` is Galois, `spectralIntegralDescend` reconstructs a point over
`F` by the coordinate inverse of `GaloisPoint.algebraicFixedEquiv` and
the existing rational/coefficient comparison. The generic group is
affine because it is isomorphic, through the supplied generic
identification, to the generic fibre of the supplied affine model;
affineness is proved internally. The extended reconstructed point is
exactly the original fixed point. The scalar-intersection membership
theorem therefore places the reconstruction in the original
`M.integralPoints`. Injectivity of coefficient extension proves the
other inverse law. These maps define the actual multiplicative
equivalence `spectralIntegralFixedEquiv`, whose forward coercion
is exactly `rationalExtend`.

These are internal derivations from the published spectral valuation,
coordinate-integrality, coefficient-conjugation and arbitrary Galois
point-descent constructions. The action and image-reflection results
require algebraicity alone; the effective fixed-subgroup equivalence
additionally requires that the extension be Galois. No result imposes
a finite-degree, reductivity or smoothness condition. The construction
applies in equal and mixed characteristic and in every universe `u`.
It supplies neither a special point nor a building embedding or comparison.
