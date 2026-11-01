# Spectral dependence of the actual dominant quotient kernel on each slice

This internal deduction uses the published determinant-weight exponent-addition
and spectral-point laws. It concerns the actual dominant raw and descended
quotient kernels, the real integral of the raw norm, and genuine rectangle
fiber integrability. It preserves the prescribed rectangle measure and adds
no convergence assertion.

The representative proof factors the determinant weight at parameter `s` into
the weight at zero times the weight with exponent `s`. Pulling the constant
out of the complex rectangle integral gives `representativeKernel_spectral`.
Applying the norm multiplication law before real integration gives
`representativeNormProfile_spectral`. The absolute value of the determinant
is nonzero, so its complex power is nonzero; integrability of the rectangle
fiber is equivalent at `s` and at zero.

Quotient induction and the published
`normalizedDeterminantWeight_eq_spectralPoint_zpow` identify the quotient
multiplier with `spectralPoint q s ^ determinantOrder`, where `q` is the
canonical residue cardinality. No representative is selected in a definition.
The norm-profile statement remains distinct from the norm of the complex
quotient kernel, and the descended fiber integrability is transported as
an equivalence.

For the supplied standard quotient measure `νN`, the new definition
`kernelSliceCoefficient ν ell f Wtest νN hr d` is precisely

```text
∫ q in TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
  quotientKernel ν ell f Wtest hr 0 q
  ∂TwoBlockLowerFixedSlice.lowerMeasure F h νN.
```

The lower measure is exactly the published pushforward of `νN` by the inverse
block-rotation quotient equivalence. No compatible measure or new
normalization is chosen. The real definition
`kernelNormProfileSliceCoefficient` replaces the complex quotient kernel
in this same restricted integral by its real raw-norm profile. Its value is
not defined as the norm of `kernelSliceCoefficient`.

On the determinant slice indexed by `d`, the published
`mem_determinantSlice_iff_determinantOrder` makes the spectral multiplier
constant. The two `*_spectral_onSlice` lemmas record the actual pointwise
identities. `setIntegral_quotientKernel_spectral` and
`setIntegral_quotientNormProfile_spectral` use measurable-slice congruence
and pull that constant out of the total Bochner integral. Thus at every
complex `s` the restricted complex integral is

```text
kernelSliceCoefficient ... d * spectralPoint q s ^ d,
```

and the restricted real profile integral has multiplier
`‖spectralPoint q s ^ d‖`. Here `q` is the canonical residue cardinality,
and `d` is an arbitrary integer, including negative values.

The two `integrableOn_*_spectral_iff` lemmas separately prove genuine
restricted integrability equivalence at `s` and at zero. Positivity of the
residue cardinality makes `spectralPoint q s` nonzero; its integer powers
and their norms are nonzero. Pointwise congruence on the measurable slice
then reduces each assertion to integrability after multiplication by a
nonzero constant. These arguments use no equality of totalized integrals
to deduce integrability.

`ae_quotientFiberIntegrable_spectral_iff` applies the pointwise fiber
equivalence almost everywhere for the same restricted lower measure.
Finally, `kernelAbsoluteIntegrable_restrict_spectral_iff` uses the published
`lowerMeasure_restrict` identity to identify that measure with
`lowerMeasure F h (νN.restrict (determinantSlice T t d))`. It assembles all
three equivalences in the existing `KernelAbsoluteIntegrable` predicate.
The coefficient and equivalences allow every supplied measure; they
require neither quotient-measure compatibility nor sigma-finiteness.
The slice integral and slice outer-integrability proofs use the Borel
structure on the lower quotient. The final restriction-transport package
uses Borel structures on both quotients.

The field and dependent block carriers have independent universes. All natural
rectangle dimensions, including zero, and all inverse block functionals,
including zero, remain present. This helper supplies neither a matrix
comparison nor a functional equation, factor existence, or either final
dominant-rank gamma/L proposition. In particular, the equivalences assert no
slice convergence by themselves and give no equivalence of whole-quotient
outer convergence at different spectral parameters. The actual analytic
first-block and dual-comparison results remain separate obligations.
