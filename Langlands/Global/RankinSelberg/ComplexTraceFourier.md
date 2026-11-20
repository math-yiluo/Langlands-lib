# Self-dual trace Fourier transformation in finite complex coordinates

`ComplexTraceFourier.transform` represents Jacquet's negative trace Fourier transform of a complex-valued Schwartz test on any finite family of complex coordinates. `ComplexTraceFourierEvaluationStatement` evaluates this Schwartz function using the Library's self-dual additive measure in each coordinate and the character at the negative sum of coordinate products.

The real Hilbert norm and ordinary product norm give a continuous linear equivalence on the coordinate space. Their volumes agree because the product of the parallelepipeds of the real orthonormal basis of the complex plane is the parallelepiped of the induced real orthonormal basis. In each coordinate, the real inner product with the conjugate of `2 * a * y` equals the field trace of `a * x * y`. The real Fourier kernel therefore gives the claimed sign. The volume factor is `2 * ‖a‖` per complex coordinate. The frequency change is a real dilation by that scale followed by a real linear isometry. Its volume Jacobian is the square of the full self-dual density.

This is a derived form of the Fourier normalization in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §2, p. 3 and §4.7, p. 30, in preparation for the matrix coefficient application.
