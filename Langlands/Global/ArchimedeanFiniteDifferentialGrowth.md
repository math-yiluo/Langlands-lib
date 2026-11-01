# Polynomial growth of enveloping derivatives of finite smooth vectors

Author: Worker 94.

`enveloping_hasPolynomialGrowth_of_finite` proves that every genuine
archimedean smooth function with finite orbit under the actual standard compact
group, finite orbit under the enveloping center, and polynomial matrix-height
growth retains polynomial growth after every element of the complex enveloping
algebra. The theorem is polymorphic in the number field universe and retains
every natural rank, including zero. There are no analytic or reproduction
premises.

The measure-parametrized helper
`enveloping_hasPolynomialGrowth_of_derivativeFinite` first chooses the actual
compact-central reproducing kernel supplied by
`compactFiniteCentralReproducingKernel`. The unconditional theorem
`compactKernelConvolutionDifferentiation` supplies a smooth lift of convolution
against this kernel and transfers every enveloping derivative to the kernel.
Pointwise reproduction identifies that lift with the original smooth function
by subtype extensionality.

For a specified enveloping element, `envelopingCompactSupport` proves that its
derivative of the kernel still has compact support. Smoothness gives continuity
of both the original function and the differentiated kernel. The unconditional
`compactKernelConvolutionGrowth` theorem then bounds the transferred integral
by a polynomial in the existing matrix/inverse height. Rewriting by the transfer
identity yields the required growth of the actual enveloping derivative. The
left Haar convention remains exactly `κ(y⁻¹ * g)`.

The exported smooth-function version installs the existing Borel measurable
structure locally and uses the Library's actual `leftHaarMeasure`. The inverse
of `compactActionEquiv` transports compact finiteness to the copy with the
derivative topology; `toSmooth` returns precisely the original smooth function.
No measure assumption remains in this version.

This is an internal composition of the actual constructions and proved results
named in the imports. Its small helper lemmas support the exact automorphic
differential-growth proof in the same contribution. It does not assert growth
for arbitrary smooth functions without the compact and center finiteness
hypotheses.
