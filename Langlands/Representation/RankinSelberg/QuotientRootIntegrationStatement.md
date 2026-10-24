# Quotient integration in root coordinates

`Langlands.RankinSelberg.QuotientRootIntegrationStatement F T n` is an
internal conditional proposition, with
`QuotientIwasawaIntegrationStatement F T n` as its explicit premise.
It retains every supplied p-adic topology, every rank `n+1` including one,
the unipotent right-invariance instance, and every compatible measure `μ`
on the actual left-unipotent quotient.

Let `A = (Fˣ)^(n+1)` with its product of normalized multiplicative Haar
measures `dA`. Let `κ` be the actual general linear Haar measure restricted
to its integral subgroup. Define

```text
d(a)_i = ∏_{j ≥ i} a_j,
q(a,z) = [diagonalUnits(d(a)) * z],
ρ(a) = (∏ i, T.normalizedAbs(a_i)^((i+1)(n-i)))⁻¹.
```

The complex weight `w(a)` has the same formula, with the positive real
absolute values cast into `ℂ` before the natural powers and product.
It equals the complex cast of `ρ(a)`. The proposition first asserts the
actual measure identity

```text
μ = q_* ((dA × κ).withDensity (a,z ↦ ENNReal.ofReal (ρ(a)))).
```

For every measurable complex function `f` on the quotient, put
`H(a,z) = f(q(a,z)) * w(a)`. The remaining conclusions are:

- `f` is integrable with respect to `μ` if and only if the iterated
  nonnegative integral `∫⁻ a, ∫⁻ z, ‖H(a,z)‖ₑ dκ(z) dA(a)` is finite.
- If `f` is integrable with respect to `μ`, its actual Bochner integral
  equals `∫ a, ∫ z, H(a,z) dκ(z) dA(a)`.

The second identity is asserted only under integrability; no use of Fubini
outside its convergence domain is hidden in the total Bochner notation.
The first conclusion includes joint measurability through the measurable
function premise and the continuous coordinate maps and weight.
There is no compact-support requirement on `f`.

This is an internal consequence of the existing Iwasawa measure proposition,
`RootCoordinateChangeStatement`, and change of variables for measures,
weighted measures, Tonelli's theorem and Fubini's theorem. The cumulative
product preserves `dA`; its product with the identity preserves `dA × κ`.
The positive-root modulus in diagonal coordinates becomes the displayed
product by the root-coordinate theorem. Transporting the density therefore
gives the measure identity with the inverse, with no normalization scalar.
The norm integral and Bochner integral then follow by pushforward, density
and product integration. This module defines only the proposition.

No new attribution to original literature is made. The Iwasawa premise
retains its separate proof obligation. Applying this interface to a JPSS
integrand also requires proving its measurability; this proposition alone
does not prove coefficient expansions, Mellin convergence, rationality,
a common denominator or normalized-generator existence.
