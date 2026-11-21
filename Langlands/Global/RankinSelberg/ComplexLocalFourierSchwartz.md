# Continuity of the complex trace Fourier transform on Schwartz space

The exact `complexFourierTransform` on Schwartz tests is represented by a continuous
complex-linear map. The proof puts the real inner product of complex Euclidean space on the
Fourier side, using the continuous linear equivalence from the coordinate space.

For input \(y\) and frequency \(x\), the inner product with the vector whose coordinates
are \(\overline{2 a x_j}\) is \(\operatorname{Tr}_{\mathbb C/\mathbb R}(a\sum_j y_j x_j)\).
The positive sign in the Fourier kernel therefore uses Mathlib's inverse Fourier transform.
The pushforward of the exact product measure is additive Haar, so it is proportional to
Euclidean volume. Pulling the inverse Fourier transform of the transported test function
back along the frequency equivalence and multiplying by this scalar gives the continuous
linear map on Schwartz space. Changing variables in its integral proves pointwise agreement.
Evaluating the map at one test also gives the individual Schwartz representative.

This internal result uses the Library definition of the positive trace Fourier transform
and Mathlib's Fourier theorem for Schwartz functions on a finite-dimensional real inner
product space.
