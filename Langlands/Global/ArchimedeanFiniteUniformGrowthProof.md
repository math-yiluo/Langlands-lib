# Fixed-exponent differential growth for finite smooth vectors

Proof authors: Workers 116 and 94. Worker 88 prepared the final documentation
and proof submission from their shared implementation.

`Langlands.Global.ArchimedeanGL.finiteUniformDifferentialGrowth` proves the
published proposition
`Langlands.Global.ArchimedeanGL.FiniteUniformDifferentialGrowthStatement K n`.
For every number field `K : Type u` and natural rank `n`, including zero,
let `f : SmoothFunctions K n` have finite-dimensional orbit under the
standard infinite compact group and under the center of the actual complex
enveloping algebra. Every supplied bound
`‖f.val g‖ ≤ C * matrixHeight K n g ^ d`, with real `C ≥ 0` and natural `d`,
then bounds every actual enveloping derivative with the same `d` and a new
nonnegative multiplicative constant depending on the derivative.

The private helper `enveloping_bound_of_derivativeFinite` adapts Worker 94's
`enveloping_hasPolynomialGrowth_of_derivativeFinite` argument. Choose the
existing actual compact-central reproducing kernel `κ` of the function via
`compactFiniteCentralReproducingKernel`. The theorem
`compactKernelConvolutionDifferentiation` supplies a smooth convolution lift
`F` and transfers each enveloping derivative to this kernel. Pointwise
reproduction from `rawConvolution_compactFiniteCentralReproducingKernel`
and subtype extensionality identify `F` with the original smooth function.
The convolution convention remains
`∫ y, f(y) * κ(y⁻¹ * g) ∂μ` for left Haar measure.

The derivative of the kernel has compact support by
`envelopingCompactSupport`, and both input and kernel derivative are
continuous. Apply `compactKernelConvolutionBound` with the supplied
`C` and `d`. Its conclusion retains this very `d` and supplies a new
nonnegative multiplicative constant. This is the only change from the
earlier argument's use of the existential growth theorem.

More explicitly, for the differentiated kernel
`η = envelopingAction K n a κ.val.val`, the imported bound takes
`D = C * ∫ z, ‖η.val z⁻¹‖ * matrixHeight K n z ^ d ∂μ`.
Continuity and compact support make this weight integrable; nonnegativity
of the weight and `C` gives `D ≥ 0`. Left invariance and submultiplicativity
of the matrix height then give the bound at every `g`. These analytic
steps are proved in `ArchimedeanConvolutionGrowthProof`, rather than added
as premises here. In particular, the proof retains every supplied `d`,
including zero, and also allows `C = 0`.

The final theorem transports compact finiteness to
`DerivativeSmoothFunctions` through `compactActionEquiv`, installs the
existing Borel structure and uses the actual `leftHaarMeasure`.
Returning through `toSmooth` gives the original smooth function.
No measure or reproducing-kernel premise survives in the theorem.
Its bound holds for every enveloping element with the same supplied exponent,
and the multiplicative constant is independent of `g`.

The proof is an internal composition of the existing Library constructions.
The [paired statement](ArchimedeanFiniteUniformGrowthStatement.md) records
the MW95 I.2.3/I.2.5/I.2.17 source route and its derived scope. Exact
preservation of every supplied natural exponent comes from the Library's
explicit convolution bound for its particular matrix/inverse height.

The result concerns actual smooth functions on `InfiniteAdelicGL K n`.
It does not supply uniform global adelic control across finite slices,
growth for general reductive groups, Siegel-domain decay, quotient-measure
results, cuspidal Hilbert-space comparison or spectral decomposition.
Those comparisons and results remain separate program obligations.
