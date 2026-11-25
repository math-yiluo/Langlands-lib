# Orbital integration of continuous compactly supported tensors

`cyclicProductConvolution` proves `CyclicProductConvolutionStatement`.
Let \(H\) be a topological group isomorphic to \(G^{m+1}\), where \(G\)
is a second-countable locally compact Hausdorff topological group.
Both groups have Borel measurable structures. The continuous twist
on \(H\) shifts the coordinates and applies a continuous endomorphism
of \(G\) at the wrap. The full ambient measure has product
normalization in these coordinates. Fix an element of \(H\) and form
the ordered product of its coordinates in \(G\). Assume the orbit map
from the latter twisted centralizer quotient is a closed embedding.
The centralizer measures are right-invariant Haar measures with the
specified pushforward correspondence, and the two quotient measures
are compatible with the ambient and centralizer measures.

For continuous compactly supported factor functions, the tensor and
its ordered convolution are continuous and compactly supported. Their
twisted orbital integrals at the two elements agree with the declared
quotient measures. The convolution integrates over the first \(m\)
coordinates, with the final coordinate fixed by the total product.
The accompanying recursion identifies this formula with the usual
ordered left-Haar convolution of the factors.

The orbital identity holds for every continuous compactly supported
function on the product, not only for tensors. For
`Φ : (Fin (m + 1) → G) → ℂ` and a measure `μ` on `G`, the fibre integral
`splitFiberIntegral μ Φ y = ∫ w, Φ (splitProductFiberChart m (y, w)) ∂Measure.pi (fun _ : Fin m => μ)`
integrates `Φ` over the fibre of the ordered product `x ↦ x₀ ⋯ x_m`
above `y`; for a tensor it is the ordered convolution
(`splitFiberIntegral_tensor (μ) (ψ) : splitFiberIntegral μ (fun x => ∏ i, ψ i (x i)) = splitFiberConvolution μ ψ`,
by definition). Under the hypotheses above,
`cyclicProductOrbitalIntegral_eq_splitFiberIntegral` states, for every
`Φ` with `Continuous Φ` and `HasCompactSupport Φ`,
`twistedOrbitalIntegral σ δ νC (fun x => Φ (κ x)) = twistedOrbitalIntegral τ β νZ (splitFiberIntegral μ Φ)`,
where `β = (List.ofFn (κ δ)).prod`. The tensor statement
`cyclicProductConvolutionOrbitalIntegral_eq` is its case
`Φ = fun x => ∏ i, ψ i (x i)`, with continuity and compact support of the
tensor from
`splitTensor_continuous_hasCompactSupport (ψ : Fin (m + 1) → G → ℂ) (hc : ∀ i, Continuous (ψ i)) (hs : ∀ i, HasCompactSupport (ψ i)) : Continuous (fun x : Fin (m + 1) → G => ∏ i, ψ i (x i)) ∧ HasCompactSupport (fun x : Fin (m + 1) → G => ∏ i, ψ i (x i))`.
The fibre integrals of Schwartz–Bruhat functions and of unit tensors are
treated in `Langlands.BaseChange.CyclicProductFiberIntegral`.

The quotient chart carries the upper quotient measure to the product
of the lower quotient measure with the free Haar coordinates. The
closed orbit embedding gives compact support of the integrand `Φ` in this
chart. Fubini gives the fibre integral at each lower orbit point. To prove
continuity of the convolution, the proof integrates over the compact
projection of the support onto the free coordinates and applies the
continuity of parameterized integrals on compact sets.

Declarations, in order: `splitFiberConvolution`, `splitFiberIntegral`,
`splitFiberIntegral_tensor`, `splitTensor_continuous_hasCompactSupport`,
`splitTensorInCoordinates_continuous_hasCompactSupport`,
`splitFiberConvolution_zero`, `splitFiberConvolution_succ`,
`splitFiberConvolution_continuous_hasCompactSupport`,
`cyclicProductOrbitalIntegral_eq_splitFiberIntegral`,
`cyclicProductConvolutionOrbitalIntegral_eq`,
`CyclicProductConvolutionStatement`, `cyclicProductConvolution`.

This is an internal extension of the split-place tensor calculation
used by Arthur–Clozel, Chapter 1, Theorem 4.5 proof, printed pp. 43–44.
The identity for arbitrary `Φ` is Henniart–Lemaire's map `φ ↦ φ*` written
as one integral; the page of `CyclicProductFiberIntegral` gives the
references.
It applies to continuous compactly supported functions at infinite
places once the split coordinates and the closed orbit map are supplied.
