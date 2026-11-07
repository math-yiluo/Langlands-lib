# Effective Galois descent of actual Lie-kernel vectors

This internal deduction concerns an affine group scheme locally of finite type
over an arbitrary field `k`, in any common universe, and a Galois extension
`L / k`. It imposes no smoothness, connectedness, reductivity, characteristic,
or finite-degree hypothesis on the extension.

`coefficientFixedLie` is the additive subgroup of the actual dual-number
identity kernel over `L` fixed by every coefficient automorphism of `L / k`.
The fixedness condition uses the existing actual `lieKernelMapLinear`.
Coefficient extension of an original-field Lie vector is fixed, and is
injective. Natural finite Lie coordinates turn injectivity into the
injectivity of the field inclusion on each coordinate.

For a fixed Lie vector, naturality of the same finite coordinates shows that
each coordinate is fixed by every field automorphism. The Galois fixed-field
theorem puts those coordinates in the image of `k`. Their unique preimages
reconstruct an actual Lie vector over `k`.
`coefficientFixedLieEquiv` bundles the resulting additive equivalence with
the original coefficient extension as its forward map.

`baseChangeFixedLie` instead uses the canonical semilinear
`baseChangeGaloisEquiv` on the Lie kernel of the actual base-changed group.
`fixedLieBaseChangeEquiv` identifies the two fixed carriers through the
actual pullback comparison. `baseChangeFixedLieEquiv` composes this with
coefficient descent, so its forward map is precisely coefficient extension
followed by the inverse actual Lie pullback comparison. The two fixed-subgroup
definitions and their pullback equivalence do not need local finite type or
Galois hypotheses; effective descent uses both.

The provenance is internal: the proof uses the published natural finite Lie
coordinates, the canonical coefficient and scheme-base-change Lie maps, and
Mathlib's Galois fixed-field theorem. It identifies actual Lie vectors, without
asserting any descent of root points, root-orbit decomposition, character
restriction transitivity, root-field parametrization or apartment existence.
