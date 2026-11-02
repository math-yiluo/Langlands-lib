# Genuine convergence on each dominant determinant slice

This internal derived result supplies convergence for the actual five-block
JPSS kernel of Section 4.10(2) (1983, printed page 419). It combines the
raw-norm envelope, the exact quotient torus integration formula, Iwasawa
coverage and the previously established spectral identities. The quantitative
threshold and the auxiliary predicates are internal deductions, rather than
separate assertions attributed to JPSS.

`exists_standard_torus_representative` proves that every actual standard
unipotent quotient point has a representative `torus(lam) * c`, with `c` in
the canonical integral subgroup. The proof applies Iwasawa decomposition to
a group representative and removes its left unipotent factor in the quotient.
It proves existence and does not choose a representative section.

`exists_summable_kernelNorm_majorant` fixes one real threshold before the
opposing twist, induced section, complementary dimensions `j,k`, their rank
equality and the ambient coefficient-image test. For every twist above the
threshold it constructs a nonnegative envelope `A(lam)` such that the exact
inverse-modulus density times `A` is summable over all integer torus vectors.
At inverse-rotated torus representatives the actual rectangle fiber is
integrable, and both the complex average's norm and the real raw-norm profile's
norm are at most `A(lam)`. The profile is the integral of the pointwise kernel
norm, retaining both rectangles and the supplied scalar Haar measure.

The proof starts with `exists_kernelNorm_torus_envelope`. At its reference
parameter `s0 = (j+k+1)/2-j`, the determinant weight equals one. Multiplying
the geometric base by the common bound for the inverse Borel modulus pays
for the quotient density. The opposing cone supplies support; outside it
the profile vanishes, and the complex average's norm is bounded by that
profile. The existing cone-geometric summability theorem then supplies one
threshold before all `j,k`. The threshold does not depend on a quotient
measure or an epsilon equation.

`kernelAbsoluteIntegrable_of_summable_torus_bound` works with an arbitrary
smooth ambient representation, actual section and supplied functionals,
and a bound satisfying its explicit hypotheses. It uses the exact supplied
compatible standard quotient measure and its prescribed lower transport.
Measurability of the complex kernel and real raw-norm profile comes from
`TwoBlockDominantKernelRegularity`. Transport by the canonical quotient
homeomorphism gives measurable functions on the standard quotient. Applying
`QuotientTorusEnvelope.integrable_of_summable_torus_bound` proves genuine
integrability of the complex kernel and of the complex embedding of the real
profile. Taking the real part recovers integrability of the profile itself.
Iwasawa coverage extends actual fiber integrability to every lower quotient
point, yielding the separate almost-everywhere clause of
`KernelAbsoluteIntegrable`. No integrability conclusion is inferred from a
totalized integral identity.

`kernelAbsoluteIntegrable_restrict` restricts all three absolute-input
conditions to a determinant slice. It uses the exact identity commuting the
prescribed lower measure with restriction of the supplied standard measure.

`IsUniformSliceConvergence` is Prop-valued. Its threshold precedes the twist,
every supplied right-invariance certificate and compatible quotient measure,
all sections, both complementary dimensions and all ambient tests. For each
such tuple it asserts measurable complex kernel and real profile at every
complex spectral parameter, actual fiber integrability at every quotient
point and every parameter, and `KernelAbsoluteIntegrable` on every actual
determinant slice at every parameter.

`exists_uniform_slice_convergence` proves that package for full Whittaker-type
ambient and block representations. It obtains global absolute input at the
reference parameter and then restricts to each determinant slice. The
nonzero constant spectral multiplier on that slice transfers convergence to
zero and to any other complex parameter. The same nonzero multiplier
transfers pointwise fiber integrability. The proof makes no assertion of
global quotient integrability at arbitrary spectral parameters.

The field, ambient carrier and dependent block carriers retain independent
universes. All positive block ranks, arbitrary complementary dimensions
including zero, reducible Whittaker-type representations and zero supplied
functionals remain allowed. This pair proves the actual lower slice
convergence prerequisites. The upper raw-product convergence and the finite
Laurent convolution identity remain separate obligations of the host task.
