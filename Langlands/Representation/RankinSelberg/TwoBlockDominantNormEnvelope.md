# Integrable rectangle fibers and their actual raw-norm envelope

This internal derived argument concerns the actual JPSS Section 4.10(2)
five-block kernel (1983, printed page 419). It combines the previously proved
raw torus majorant with the exact supplied product Haar volume of the two
rectangle boxes. The quantitative envelope and its reference parameter are
internal deductions, rather than separate assertions attributed to JPSS.

`kernel_referenceParameter` uses
`s0 = (j+k+1)/2-j`. At this parameter the entire determinant exponent is zero,
so the actual weighted kernel equals `rawKernel` pointwise. This identity
retains both rectangles and all their entries.

`rectangleMeasure_box_ne_top` proves that the simultaneous rectangle box has
finite volume for the supplied scalar additive Haar measure `nu`.
`fiber_integrable_normProfile_le_of_box` bounds the actual kernel norm by a
constant times the indicator of that box. Measurability and this integrable
majorant prove genuine rectangle fiber integrability. The triangle inequality
bounds the norm of the complex rectangle integral by the integral of the raw
norm. Monotonicity bounds the latter by the real volume of the box times the
same constant. This proof works with the integral of the pointwise norm,
without inferring its integrability from the norm of the complex average.

`rectangleMeasure_real_box` computes the real volume as
`nu.real(O)^d * (q^d)^e`, with
`d = (m 0+1)*k + j*(m 1+1)` and canonical residue cardinality `q`.
It retains the supplied Haar normalization. The rank equalities imply
`d <= 2*(r+1)*(r+1)`; splitting `e = N+L` absorbs the fixed factor into a
constant and bounds the varying factor by
`(q^(2*(r+1)*(r+1)))^L`. Empty rectangle dimensions satisfy the same formulas.

`IsKernelNormTorusEnvelope` is Prop-valued. Its inputs fix the geometric base
before the real opposing twist, induced section, complementary dimensions
`j,k`, their rank equality and the actual ambient coefficient-image test.
For each such tuple it chooses a nonnegative constant and cone cutoff before
all torus exponents and integral right factors. At the actual representative
`blockRotation^-1 * torus(lam) * c` and reference parameter `s0`, it asserts
fiber integrability, the complex-average norm bound by the real raw-norm
profile, nonnegativity of that profile, and the profile bound
`C * B^torusSize(lam) * q^(-u*twistDegree(lam))`.
A nonzero profile also forces the opposing cone for the initial interval
`Iic a.castSucc`.

`exists_kernelNorm_torus_envelope` assumes full Whittaker type for the ambient
representation and both block representations and requires `a.val = m 1`.
It obtains the raw-kernel base before all later inputs and multiplies it by
`q^(2*(r+1)*(r+1))` to pay for variable box volume. Kernel continuity supplies
measurability. The raw majorant supplies both the uniform norm bound and the
actual support boxes, so the finite-volume lemma applies. Outside the cone,
every raw value is zero; hence its actual norm integral is zero. This gives
the asserted profile support without selecting a nonzero integrand point.

The field, ambient coefficient carrier and dependent block carriers retain
independent universes. All positive block ranks, complementary dimensions
including zero, reducible Whittaker-type representations and supplied
functionals including zero remain present. This result establishes fiber
convergence at the displayed torus representatives and a profile bound. It
does not establish quotient integrability, convergence at arbitrary spectral
parameters, or the host task's Laurent identity.

The accompanying `TwoBlockDominantSliceSpectral` pair preserves its existing
mathematical declarations and proofs. Its five canonical field local
instances receive module-specific names so that combined imports with the
support modules elaborate without generated-name collisions.
