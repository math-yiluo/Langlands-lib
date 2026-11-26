# Smooth right convolution on actual adelic points

`AdelicRightConvolutionDifferentiationStatement` uses the right convolution and smooth adelic test functions of `AdelicLocalFinitenessStatement`. The input function is measurable and locally integrable for Haar measure. Convolution with a test kernel is defined by a convergent integral at every point and produces a smooth adelic function. Its archimedean derivative along a positive right orbit is convolution with the differentiated kernel. At a kernel argument `a`, this derivative differentiates `t ↦ h(t⁻¹a)` at the identity of the infinite adelic factor. The differentiated kernel is a test function supported in the original topological support.

The proof changes variables by left Haar invariance to put the output point in the kernel. One compact integration set then contains all relevant translated supports on a neighborhood of any point of a fixed infinite slice. The finite variable of the kernel is read through the cosets of its open left stabilizer, using inversion to obtain a right quotient. This quotient is discrete, so it gives a zero-dimensional manifold parameter. The compact manifold integration theorem with an integrable scalar weight yields smoothness and the derivative formula. The original left finite stabilizer fixes the output on the right by the same Haar change of variables.

This is the derivative transport used in the smooth part of Bernstein–Lapid §7.4, Lemma (2), p. 216, and in Mœglin–Waldspurger I.2.5, p. 27. The Lean proof uses the actual adelic product manifold and the same archimedean tangent orbit as the Library's smooth automorphic functions.

`integrable_kernel_mul` gives integrability of the compactly supported kernel against each left translate of the locally integrable function.
