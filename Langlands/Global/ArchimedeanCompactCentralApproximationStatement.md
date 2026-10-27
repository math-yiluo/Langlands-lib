# Localized compact-central convolution approximation

`Langlands.Global.ArchimedeanGL.CompactCentralConvolutionApproximationStatement K n`
asks for compact smooth convolution kernels on the actual
`InfiniteAdelicGL K n`. It retains every number-field universe and every
natural rank, including zero, and uses the original topology and actual
`standardInfiniteCompact K n`.

Fix a Borel-compatible measurable structure, any left Haar measure `μ`, an
actual `DerivativeSmoothFunctions K n` member `f`, a neighborhood `V` of `f`
in the full derivative compact-open topology, and any identity neighborhood
`U` in the group. The proposition asks for an actual `SmoothCompactKernel`
`κ` with all of the following properties:

- Its closed support is contained in `U`.
- Its values have nonnegative real part and zero imaginary part, and its
  real part at the identity is strictly positive.
- Its complex inverse-kernel integral is one:
  `∫ x, κ(x⁻¹) dμ(x) = 1`.
- It is invariant under conjugation by every member of the actual compact
  subgroup: `κ(k⁻¹*x*k) = κ(x)` for every group point `x`.
- The raw convolution of `f` with `κ` has an actual smooth lift `F` in `V`,
  with the displayed equality at every point, rather than only almost
  everywhere.

The smooth lift uses the existing linear equivalence
`DerivativeSmoothFunctions.toSmooth`. The convolution is exactly the
published `rawConvolution`, whose values are
`∫ y, f(y) * κ(y⁻¹*x) dμ(y)`. Both input and output smooth functions retain
the published genuine real manifold smoothness. The topology on their
synonym is the full enveloping-derivative compact-open topology, and is
not silently replaced by a pointwise topology.

The kernel may depend on `μ`, `f`, `V` and `U`. The target asserts this
neighborhood-by-neighborhood existence; it chooses no sequence, net or
canonical kernel family. No measurable structure or Haar measure on the
compact subgroup is supplied as an assumption.

This is an internal assembly target, with no external source attribution.
A prospective proof first uses ordinary compact-kernel convolution
approximation to obtain a sufficiently small support neighborhood,
intersects it with `U`, and uniformly shrinks that intersection under
compact conjugation. It chooses a normalized nonnegative kernel in the
shrunken neighborhood and averages it with a probability Haar measure on
the actual compact subgroup. The averaging support bound, invariance,
identity value and inverse-integral preservation give the required kernel;
ordinary approximation then supplies `F`. Those inputs and the assembly
are separate proof obligations. This file defines the proposition only.

This target adds an actual localized conjugation-invariant approximating
kernel to ordinary convolution approximation. It does not assert compact
type preservation, finite multiplicities, an exact reproducing kernel,
analytic regularity, or polynomial growth of automorphic derivatives.
Those require further arguments against their actual published carriers.
