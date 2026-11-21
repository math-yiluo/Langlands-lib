# Integration of a derivative on a finite-dimensional function space

`functionBasisEvaluation` evaluates a basis of complex functions at a point, giving a vector of values. For every point `x`, let `c x` be a real-parameter curve with `c x 0 = x`. Suppose each function in the space has a derivative along these curves, with that derivative given by a fixed linear endomorphism of the space. The vector of basis values then satisfies a linear differential equation with a constant endomorphism. Multiplying the vector by the exponential of the negative endomorphism times the parameter gives a function of derivative zero. Its value at zero is the basis evaluation at `x`.

`function_comp_flow_mem` expands the resulting exponential action in the basis. The coefficients depend on the endomorphism and the curve parameter. Consequently, precomposing a function with the given curve at that parameter stays in the same function space. The statement treats the underlying domain as a type. Differentiability is required only for scalar functions along the specified curves.

This is a derived analytic lemma for proving finite idele-centre orbits in the step using Langlands, *On the notion of an automorphic representation* (1979), Lemma 6, printed p. 205.
