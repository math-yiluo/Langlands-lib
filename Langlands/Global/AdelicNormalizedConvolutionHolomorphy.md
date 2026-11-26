# Entire coefficients from finite span on the imaginary axis

`IsIwasawaCompact.differentiable_integral_translate` evaluates the
integrated normalized right action at a fixed adelic point. Its scalar
integrand is the product of the kernel, the inducing form evaluated at
the translated point, and the exponential of the parameter paired with
the change in height. The integrand vanishes outside the compact kernel
support. Joint continuity bounds it on the product of that support and
each compact parameter set. The holomorphy theorem for parametric
integrals then applies to the Haar measure restricted to that support.

Given a finite spanning family for the convolutions at imaginary
parameters, `IsIwasawaCompact.exists_finiteNormalizedConvolutionExpansion_of_span_imaginary`
extracts the coefficients of an independent subfamily by continuous
linear combinations of evaluations. Each coefficient is entire, and
pointwise equality holds on the imaginary axis. In the complexification
of real parameter coordinates, the identity theorem on the totally real
subspace \(i\mathbb R^n\) gives pointwise equality throughout the complex
parameter space. Each output spanning form comes from the supplied
family and retains its stated property.

`normalizedConvolutionFiniteSpan_of_imaginarySpan` applies this argument
to the square-integrable inducing forms of a presented parabolic. Its
hypothesis `NormalizedConvolutionImaginarySpanStatement` asks for a
common finite span only on imaginary parameters. The argument uses the
normalized action in Arthur, *An introduction to the trace formula*,
§7 pp. 32–34, in the normalization of Lapid, *On the asymptotic inner
product of truncated Eisenstein series*, §2 p. 311.
