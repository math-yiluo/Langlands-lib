# Covariance of finite intertwining expansions under convolution

For a fixed compactly supported continuous kernel, suppose that the normalized
average of one source form has a finite expansion, and that the normalized
averages of the target forms in a finite intertwining expansion also have finite
expansions. The predicate `IsFiniteNormalizedConvolutionExpansion` specifies these
expansions. The kernel is integrated against ambient adelic Haar measure, and
the coefficients are entire in the indicated parameter spaces. Supply finite meromorphic intertwining expansions
for the original form and for each basis form used in its averaged expansion,
with their holomorphy domains containing the imaginary axis.

`continuedIntertwining_integral_translate` identifies the two iterated
expansions at every imaginary source parameter and adelic evaluation point.
The source expansion first averages and then intertwines. The target expansion
first intertwines and then averages at the Weyl-transported parameter. Weyl
parameter transport is a complex linear equivalence and the formula composes
the target averaging coefficients with this equivalence. Finite sums and
products preserve meromorphy on the intersection of their holomorphy domains.
The defining operators agree for sufficiently regular parameters by regular
covariance and linearity of the convergent integrals. Scalar meromorphic
uniqueness on the nonempty open regular region proves agreement on the common
holomorphy domain, which contains the imaginary axis.

This carries the intertwining identity in Arthur, *An introduction to the
trace formula* (2005), §7, printed pp. 34–35 (volume PDF pp. 46–47), from the
regular region to the axis in the presence of the finite expansions. The
registered source is `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`,
SHA-256 `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
