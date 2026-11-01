# Natural GL₁ weights in the compact Fourier and block identity

This internal derived prerequisite combines CompactOrbitIntegration with
ScalarHaar. It transports the actual same-kernel Fourier/complementary-block
identity to the canonical multiplicative GL₁ Haar with determinant exponent
one. It does not assert a model-vector comparison or a gamma functional equation.

`compactSignedWeylGLIntegrand` is the compact Fourier-orbit average integrated
over the actual unipotent Haar, evaluated at the only entry of a GL₁ element,
and multiplied by its determinant weight of exponent one.
`compactSignedBlockGLIntegrand` does the same with the original test and the
actual complementary block, which remains a free rectangular matrix variable.
Both definitions keep the original compact measure, Schwartz kernel, continuous
translate map, test and character.

The theorem `compact_signedWeylGL_blockGL_fourier_duality` first obtains
integrability of the scalar average and the full scalar/block average from
CompactOrbitIntegration. ScalarHaar transports these to genuine integrability
on GL₁ and on the full product GL₁ × Mat(m,1). Thus convergence on the latter
product is proved, rather than inferred from convergence after block integration.
Its two integral formulas introduce exactly the same inverse positive
`GLDeterminantDensity.rectangularHaarScalar F ν 0`. Multiplying the additive
identity by this common factor proves the GL₁ identity, with no remaining scalar.
The `_iterated` theorem applies Fubini using this product integrability and also
proves integrability of the block-integrated function on GL₁.

The scope retains every canonical p-adic field, arbitrary bundled nontrivial
additive character, and the same supplied self-dual scalar Haar `ν`. The
rectangular block measure is formed from that `ν`, while GL₁ Haar is the actual
canonical `generalLinearHaar`. The size is `m+2`, including `m=0`. The parameter
measure is s-finite and finite on compact sets, and the continuous right
translate needs determinant norm one only where the kernel is nonzero. All
signed matrices, inverse-transpose operations and inverse characters are those
of the actual inherited orbit kernels. There is no representation hypothesis,
spectral parameter or rational continuation in this result.
