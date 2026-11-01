# Actual dominant rectangle quotient kernels

This is derived integration and descent data for the actual raw kernel of
Jacquet–Piatetski-Shapiro–Shalika (1983), Section 4.10(2), printed page 419,
zero-based PDF page 53. The registered source is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The displayed source formula was visually checked; the reader's page 54 is
one-based. No source-specific errata record was found in project or Library
notes. The source displays an outer quotient integral with inner rectangle
integration. The named quotient functions and their Haar/descent packaging
here are internally derived formalization tools.

The field has its canonical topology and Borel structure. The field universe
`uF` and the dependent block-carrier universe `uW` are independent. There is
no restriction on the actual dependent complex modules, block
representations, inverse-character functionals, lower normalized section,
standard test Whittaker function, or complex parameter. In particular the
inverse-character functionals may be zero. The two positive block sizes
are `m 0 + 1` and `m 1 + 1`; `j,k` may independently be zero.

For the exact supplied additive Haar `ν`, all rectangle integrals use
`rectangleMeasure F m j k ν`, definitionally

```text
(rectangularMeasure ν (m 0 + 1) k).prod
  (rectangularMeasure ν j (m 1 + 1)).
```

An empty rectangle carries the unit point mass on its unique zero matrix.
The Haar helper handles the empty dimensions by the same finite-product
scaling theorem. No Haar measure is selected or rescaled.

`representativeKernel` integrates the published actual weighted `kernel`
over these two rectangle variables at a group element `g`.
`representativeKernel_lowerBlockUnipotent_mul` first applies the published
`kernel_covariance`: translating `g` by an actual lower-group element
changes both rectangle variables by `rectangleChange`. The proved
`integral_rectangleChange` then removes that change using the exact
supplied product measure. This proves left invariance after integration.

`quotientKernel` uses `QuotientIntegration.descend` to descend that
left-invariant function to the actual `LowerQuotient h F.Carrier`.
`quotientKernel_mk` is the exact representative integral formula, by
reflexivity. No coset representative is chosen.

`representativeNormProfile` instead integrates the real norm of the
published raw weighted kernel over the same rectangles.
Its left-invariance proof applies the norm to the same pointwise
covariance and then uses the same Haar change of variables.
`quotientNormProfile` descends this real function;
`quotientNormProfile_mk` exposes the integral of the raw norm. This
construction does not replace that integral by the norm of the complex
rectangle integral.

`FiberIntegrable` means actual complex Bochner integrability of the
rectangle fiber at `g`. The theorem
`fiberIntegrable_lowerBlockUnipotent_mul_iff` rewrites the fiber by the
published covariance and uses `integrable_rectangleChange_iff`, so it
establishes both directions of actual integrability under translation.
Propositional extensionality converts this equivalence to the equality
needed for `quotientFiberIntegrable`, a Prop-valued quotient function.
`quotientFiberIntegrable_mk` is its exact representative equivalence.

The complex and real integrals are total Bochner integrals. A nonintegrable
integrand has integral zero by that convention. None of these data or
descent laws claims arbitrary-input fiber convergence, outer convergence,
or a Fubini exchange. In particular a totalized norm-profile value cannot
certify actual fiber integrability.

`outerKernelIntegral` integrates the actual `quotientKernel` against
`TwoBlockLowerFixedSlice.lowerMeasure F h νN`, the published lower measure.
`outerKernelIntegral_eq` gives the exact evaluation formula

```text
outerKernelIntegral ν ell f Wtest hr s νN =
  integral q, quotientKernel ν ell f Wtest hr s q
    with respect to Measure.map (lowerToStandard h F.Carrier).symm νN.
```

`outerKernelIntegral_standard` evaluates the same total complex integral
over the standard quotient, with integrand
`quotientKernel ν ell f Wtest hr s ((lowerToStandard h F.Carrier).symm q)`
and the same supplied `νN`. The generic outer helper proves this by the
actual quotient homeomorphism's measurable equivalence.

These constructions retain every supplied standard quotient measure.
In particular they retain every `νN` satisfying
`standardCompatible F hN νN`, for each supplied right-invariance
certificate `hN` of the exact existing `unipotentHaar F.Carrier t`.
That predicate is precisely compatibility with the existing
`generalLinearHaar F.Carrier t` and `unipotentHaar F.Carrier t`.
The generic helper proves sigma-finiteness for every such compatible
measure and its prescribed lower transport. No measure, certificate or
normalization is newly selected.

`KernelOuterIntegrable` means actual outer integrability of
`quotientKernel`. `KernelNormProfileIntegrable` means actual outer
integrability of `quotientNormProfile`, the integral of the raw norm.
`KernelAbsoluteIntegrable` specializes the helper's `AbsoluteInput` to
these actual two functions and `quotientFiberIntegrable`. The exact
equivalence `kernelAbsoluteIntegrable_iff` expands it as the conjunction
of the first two conditions and almost-everywhere actual fiber
integrability with respect to the same lower measure.
`kernelAbsoluteIntegrable_standard_iff` transports all three conditions
to the supplied standard measure by the helper's actual integrability
and almost-everywhere transport laws. None of these conditions is
asserted for arbitrary section or coefficient inputs.

This unit supplies no Section 4.10 analytic identity, outer convergence,
Fubini exchange, first-block functional equation, reversed-dual section
or Fourier comparison, parameter continuation, rational factor identity,
or final dominant base proposition. It uses no later multiplicativity.
The descent and measure laws require no smoothness, irreducibility,
full Whittaker type, factor certificates or convergence premises.
