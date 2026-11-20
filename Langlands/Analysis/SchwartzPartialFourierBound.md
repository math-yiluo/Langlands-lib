# Weighted value bounds for a partial Fourier transform

`SchwartzPartialFourier.schwartzPartialFourierBound` bounds the weight seminorms of derivative order zero of the partial Fourier transform by a continuous seminorm of the input Schwartz function. Both variables range over finite-dimensional real inner-product spaces.

In the unchanged coordinate, the absolute Fourier integral is bounded using a polynomially decaying integrable function of the integration variable and the input weight seminorms. In the frequency coordinate, each slice of the input is Schwartz. Its seminorms are bounded uniformly in the unchanged coordinate because the slice map is an affine inclusion whose linear part has norm at most one. Continuity of the ordinary Fourier transform on the Schwartz space of the second factor then gives the frequency estimate. The product norm is the maximum of the two coordinate norms, so the sum of the two controlling seminorms gives the result.

The slice identity also gives complex linearity of the partial transform. A fixed linear change of coordinates on the output costs at most the larger of one and the norm of its inverse, raised to the weight order. This gives the weighted value bound after continuous linear input preprocessing, fixed output coordinate changes, and constant scaling.
