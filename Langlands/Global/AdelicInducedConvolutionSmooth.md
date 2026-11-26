# Smooth slices of adelic induced convolution

`Langlands.Global.AdelicGroupPoints.InducedConvolutionSmoothSlicesStatement` asserts that the
actual integrated induced action `hK.inducedConvolution λ φ v` has plot-smooth infinite slices.
The data are a maximal adelic Iwasawa compact, the relative smoothness datum for the group,
a continuous compactly supported kernel `φ`, and an adelically smooth `v`. Adelic smoothness of
`v` supplies a continuous function, plot-smooth infinite slices and a right finite level.
The module also proves continuity of the integrated induced action for continuous `v`.

## Implemented proof

`rightConvolution_plotSmoothSlice_of_smoothInput` treats ordinary right convolution of `f`
with a continuous compactly supported kernel. For a fixed finite component `b` of the output,
the integrand contains `f(a c, b d)` for infinite components `a, c` and finite integration
component `d`. The right level of `f` allows the variable `d` to pass to the quotient by that
open subgroup. The quotient is discrete, so the kernel is jointly smooth in `a`, `c` and the
quotient coordinate. The proof restricts integration to the compact support of `φ` and uses
`compactManifoldIntegrableWeight` on this jointly smooth kernel, with the values of `φ` as
the weight. Smoothness of the resulting infinite slice follows from the comparison between
plot-smoothness and manifold smoothness. Continuity on the full adelic group follows separately
from locally uniform compact-support domination of the continuous integrand.

`inducedConvolutionSmoothSlices` decomposes the integrated action as twisting `v`, ordinary
right convolution and untwisting the output. The scalar Iwasawa height pairings are smooth
on infinite slices by `IsIwasawaCompact.hasSmoothHeightPairings_of_maximalCompact`. Thus the
height powers preserve smoothness. They are also right `K`-invariant, so intersecting the
right level of `v` with the open finite part of `K` gives a right level of the twisted function.
The ordinary convolution result applies to this twisted input. Pointwise multiplication by
the inverse height power gives smooth infinite slices of the induced convolution.

## Provenance

This is the smoothness step of the derivation of `InducedConvolutionFiniteSpanStatement`.
The kernel integrates the induced translates of J. Arthur, *An introduction to the trace
formula*, §7, printed p. 33 (PDF p. 45), with the half-modulus incorporated into the inducing
function. The volume is registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
The compact parametric integration argument differentiates the inducing function through the
integral.
