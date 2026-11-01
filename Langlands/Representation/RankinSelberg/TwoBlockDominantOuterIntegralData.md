# Outer integration for the actual dominant lower quotient

This is derived integration infrastructure for Jacquet–Piatetski-Shapiro–Shalika
(1983), Section 4.10(2), printed page 419, registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The displayed source integral is over the actual lower-block-unipotent left
quotient. The names and predicate packaging here are internal constructions;
JPSS does not state these as separate definitions or claims. The actual
rectangle-integrated kernel is supplied by `TwoBlockDominantQuotientKernelData`.

Every field `F : PadicField.{uF} p`, with `p` prime, uses its canonical topology,
valuation and local-field structures. The block ranks are `m 0+1` and `m 1+1`,
with their supplied sum proof `h`; both are positive by construction. Borel
measurable structures are retained on the standard quotient and actual lower
quotient. No representation hypotheses occur in this helper: its arbitrary
functions `K`, `N`, and `P` will be specialized to the complex kernel, real norm
profile, and actual fiber-integrability predicate by the entry module.

`TwoBlockLowerFixedSlice.lowerMeasure F h nuN` is used directly. Its exact
evaluation law, recorded by `lowerQuotientMeasure_eq_map`, is

```text
TwoBlockLowerFixedSlice.lowerMeasure F h nuN =
  Measure.map (lowerToStandard h F.Carrier).symm nuN.
```

The supplied standard measure is retained without a choice, rescaling or new
normalization. `outerIntegral F h nuN K` is the complex Bochner integral of `K`
against this exact lower measure. `outerIntegral_eq` gives the map-measure
formula directly. `outerIntegral_standard` evaluates it as the integral of
`K ((lowerToStandard h F.Carrier).symm q)` against `nuN`, using the existing
canonical quotient homeomorphism as a measurable equivalence. This is an
operation on quotient elements and chooses no coset representatives.

`integral_lowerQuotientMeasure` gives the same transport for every complete real
normed target, including the real norm profile. These are total Bochner integral
identities and do not require convergence. `integrable_lowerQuotientMeasure_iff`
separately transports actual `Integrable` in both directions.
`ae_lowerQuotientMeasure_iff` transports arbitrary almost-everywhere predicates
using the measurable embedding of that equivalence, without requiring
measurability of the predicate itself.

`OuterIntegrable` means actual outer integrability of the complex function `K`.
`NormProfileIntegrable` means actual outer integrability of the supplied real
function `N`. `AbsoluteInput` is the conjunction of these two conditions and
`P q` for almost every actual lower quotient element. Its intended use takes
`N` to be the integral of the norm of the raw rectangle kernel, and `P` to be
actual rectangle-fiber integrability. It does not take `N` to be the norm of
`K`. The fiber clause is explicit because a totalized integral of a norm can be
zero when that fiber is not integrable. No condition is inferred from an
integral value, and no arbitrary-input convergence is asserted.
`absoluteInput_standard_iff` transports all three clauses using the same
supplied measure and quotient equivalence.

`standardCompatible F hN nuN` retains every supplied right-invariance
certificate `hN` for the exact existing `unipotentHaar F.Carrier t`. It is
precisely `QuotientIntegration.IsCompatible` for that measure, the exact existing
`generalLinearHaar F.Carrier t`, and the supplied standard quotient measure
`nuN`. This definition chooses neither a certificate nor a compatible measure.
The outer constructions above apply to every standard measure, hence in
particular to each such compatible measure and certificate.
`standardCompatible_sigmaFinite` proves sigma-finiteness of every compatible
standard measure and its prescribed lower transport: compatibility gives
regularity; the standard quotient is Hausdorff, locally compact and second
countable; regularity then gives sigma-finiteness, which the measurable
equivalence transfers to the lower measure.

This module asserts no Section 4.10 analytic identity, outer convergence,
Fubini exchange, functional equation, parameter continuation, rational factor
identity or final dominant proposition. Empty rectangles are handled by the
separate rectangle Haar and kernel descent modules and do not alter this outer
quotient measure.
