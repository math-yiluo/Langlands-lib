# Leading Euler coefficients under native finite-flat pullback

`finiteFlatPullbackEulerLeadingCoefficient` proves the unchanged
`FiniteFlatPullbackEulerLeadingCoefficientStatement` in arbitrary universe `u`.
For an actual finite flat endomorphism over the field and an actual ample line
bundle, the leading coefficients of any two rational polynomials representing
the original and pulled-back Euler characteristics satisfy

```text
Q.leadingCoeff = (f.left.finrank x : rational) * P.leadingCoeff
```

at every target point `x`. This is an internal assembly of the published
native finite-flat Euler-difference theorem, the proved actual ample Euler
polynomial theorem, and rational-polynomial comparison. Its original source
specialization is documented in the paired statement. It introduces no extra
geometric or numerical premise.

The helper `smoothProperFiniteFlat_eulerPolynomial_leadingCoeff` first handles
a source polynomial already known to be nonzero of exact degree `g`. The
published `smoothProperConnectedFiniteFlatGeometry` supplies integrality,
actual topological dimension `g`, and positivity of the native rank of the
finite flat map. Smoothness and properness supply the Noetherian and separated
instances used by the coherent Euler theory. The over-category equation
`f.w` identifies the composite structure map with the original structure map.

The actual native-rank comparison is
`finiteFlat_topEulerDifference_eq_zero`, imported from
`FiniteFlatEulerPolynomialCoefficientProof`. Its implemented geometric route
uses a generic free chart for the actual finite locally free structure-module
pushforward, with rank given by `f.left.finrank x`; coherent comparison away
from smaller support, finite-free Euler additivity, and the actual affine
projection formula then give vanishing of the `g`-fold forward difference of

```text
n ↦ Q(n) - (f.left.finrank x : rational) * P(n).
```

Thus no numerical degree or rank certificate is assumed. The supplied
polynomial evaluation identities turn that geometric Euler identity into the
polynomial difference identity. The published rational-polynomial comparison,
with nonzero native rank and nonzero source polynomial, yields exact degree
`g` for `Q` and the displayed leading-coefficient formula.

For the target theorem, `smoothProperLineBundleEulerPolynomial` supplies an
actual ample Euler polynomial `A` of exact degree `g` and strictly positive
leading coefficient. Equality of the actual Euler evaluations identifies the
arbitrary supplied `P` with `A` by polynomial uniqueness. Consequently `P` is
nonzero of exact degree `g`, so the helper applies. Choices of finite-cohomology
proof do not change the Euler invariant. The theorem covers arbitrary fields,
arbitrary characteristic, and `g = 0`; it assumes no polarization identity.
