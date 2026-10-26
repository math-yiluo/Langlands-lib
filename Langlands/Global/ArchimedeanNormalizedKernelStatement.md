# Normalized compact smooth kernels in identity neighborhoods

`Langlands.Global.ArchimedeanGL.NormalizedCompactKernelStatement` is an
internal proposition defining a kernel-existence obligation. This module does
not prove it. It uses every number field `K : Type u` and every natural rank
`n`, including zero.

Write `G = InfiniteAdelicGL K n`, with its existing completion-based topology.
For every Borel-compatible measurable structure on `G`, every left Haar
measure `μ`, and every set `U` belonging to the neighborhood filter of the
identity, the statement asks for `κ : SmoothCompactKernel K n` satisfying:

- The closed support `tsupport κ.val.val` is contained in `U`. Membership in
  `SmoothCompactKernel` also requires this support to be compact and the
  underlying function to belong to the published actual smooth-function space.
- Every value has nonnegative real part and zero imaginary part. Thus the
  kernel takes values in the nonnegative real numbers embedded in `ℂ`.
- The real part of its value at the identity is strictly positive.
- The complex integral `∫ g, κ.val.val (g⁻¹) ∂μ` equals `1`.

The quantification includes all identity neighborhoods, which need not be
open or conjugation invariant. The kernel may depend on the measurable
structure, measure, and neighborhood. The Haar hypothesis supplies finiteness
on compact sets and positivity on nonempty open sets; it includes the
nonzero-measure requirement. No normalization of the given Haar measure is
imposed.

The integral uses the inverse kernel deliberately. For the published
convolution convention

```text
(f * κ)(x) = ∫ y, f(y) κ(y⁻¹x) dμ(y),
```

the left-Haar substitution `y = xz` gives the averaging weight `κ(z⁻¹)`
against the positive right translations `f(xz)`. Its integral must therefore
be one. This normalization requires no inversion invariance or unimodularity
assumption. The statement itself asserts the displayed normalization; it
does not prove a change-of-variables formula. Since inversion is continuous
at the identity, placing `κ` in arbitrarily small identity neighborhoods also
places its inverse-kernel weights in arbitrarily small identity neighborhoods.

This is an internal local analytic prerequisite formulated using
`ArchimedeanConvolution`'s existing group, smooth kernels, and Haar measures.
It separates existence of normalized kernels from convergence of their
convolutions. A prospective proof can choose a nonnegative real smooth bump
at the identity and divide by the positive integral of its inverse. The
pinned Mathlib manifold bump-function API supplies
`SmoothBumpFunction.nhds_basis_tsupport`; adapting that API to the published
smooth carrier and proving the integral properties are proof obligations.
This module contains only the proposition and a parameter-shape example.

No compact-conjugation invariance, convolution convergence, smooth lift of
convolution, integration in the derivative topology, reproducing kernel,
admissibility, analytic regularity, or automorphic derivative-growth result
is asserted. Those remain separate obligations.
