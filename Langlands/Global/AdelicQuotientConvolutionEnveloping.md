# Differentiating convolution representatives on the positive rational quotient

`exists_convolution_enveloping_representative` compares two operations for a
continuous Hilbert action and a continuous intertwiner into `L²` of the
positive rational quotient. Start with a vector fixed by a compact open
subgroup of the finite factor. A smooth compact archimedean kernel gives a
smooth convolution vector. The lifted kernel gives the pointwise quotient
convolution of the image of the original fixed vector. For each element of
the complex enveloping algebra, the theorem gives a continuous left invariant
function whose slices are the corresponding derivatives of the pointwise
convolution. Its quotient function is almost everywhere the image of the
same derivative of the Hilbert convolution vector.

For every smooth compact kernel, the comparison at the identity in the
enveloping algebra follows by moving the continuous intertwiner through the
Bochner integral and applying `positiveQuotientLpSmoothing_ae_eq`. For a Lie
generator both `lieDerivative_gardingIntegral` and
`adelicRightConvolutionDifferentiation` move differentiation onto the kernel.
`liftArchimedeanKernel_derivative` identifies those differentiated kernels.
Induction on the enveloping algebra uses this step for left multiplication
by a generator and linearity of both integrals for sums and scalar multiples.
Thus a single differentiated kernel gives the two representatives at each
step. The proof uses integrability of the original and differentiated compact
kernels against the respective orbits or locally integrable quotient functions.

The comparison is derived from Gårding differentiation of the integrated
action and differentiation of scalar convolution. The underlying right
convolution is the one in Mœglin–Waldspurger, *Spectral decomposition and
Eisenstein series* (1995), I.2.5, p. 27. [Adelic kernel differentiation](AdelicRightConvolutionEnveloping.md)
