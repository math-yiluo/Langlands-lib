# Integral transporters preserve containment in translated apartments

Author: Worker 362.

This internal unit connects an actual integral transporter to containment in
an actual conjugate valuation apartment. It uses
`IntegralModel.HenselianTransporter` and the published
`KPApartmentData.conjugateApartmentMap` realization.

Work in an arbitrary universe `u` with a commutative domain `R`, its fraction
field `K`, and a supplied `M : IntegralModel R K G`. Let
`A : M.TransporterData j₁ j₂ g₀` be the actual transporter data specified in
the paired algebraic module. Let `T` be a commutative group scheme over
`K`, let `i : T.toGrp ⟶ G` have a monomorphic underlying scheme map, assume
the structural morphism of `G` is affine, and supply
`D : KPApartmentData i ω` for a function `ω : Kˣ → ℝ`.

For `q ∈ G(K)`, `D.integralTransporterApartmentMap A q` is the actual map
from `D.Apartment` into the original quotient `D.ReducedBuilding` given by

```text
x ↦ (A.genericPoint * q) • D.apartmentMap x.
```

The theorem `subset_range_integralTransporterApartmentMap` assumes
`M.integralPoints ≤ fixingSubgroup G(K) Y` and that the chart
`x ↦ q • D.apartmentMap x` covers a subset `Y`. It proves that the new
map also covers `Y`. For `y ∈ Y`, choose an original chart preimage `x`.
The integral membership theorem for `A.genericPoint` shows that it fixes
`y`. Associativity of the group action then gives
`(A.genericPoint * q) • D.apartmentMap x = y`.

To realize this conclusion as a conjugate valuation apartment, supply another
commutative group scheme `T'`, an inclusion `i' : T'.toGrp ⟶ G` with
monomorphic underlying scheme map, an actual isomorphism `e : T ≅ T'`, and
the conjugation square

```text
i ≫ (G.innerIso (A.genericPoint * q)).hom =
  CommGroupScheme.groupHom e.hom ≫ i'.
```

`subset_range_integralTransporter_conjugateApartmentMap` proves that the
same subset `Y` lies in the image of
`D.conjugateApartmentMap e (A.genericPoint * q) h`. Its domain is the
apartment of the actual transported data
`D.transport e (G.innerIso (A.genericPoint * q)) h`. The proof transports
the chart preimage by `D.apartmentTransportEquiv` and uses the published
`conjugateApartmentMap_transport` equality. The quotient is still the original
`D.ReducedBuilding`, with its original rational-point action.

The algebraic module also proves the actual generic conjugation equation
of the recorded transporter. In this geometric module the displayed square
for `i` and `i'` is retained explicitly: those maps are not assumed to be
the two generic maps occurring in `A`. Likewise the initial covering chart
and the model integral-point fixer inclusion remain substantive inputs.
No maximality, splitting, centralizing property, specialness, building
availability, or initial apartment existence is asserted here. The result
does not prove `UnramifiedFixedPairSpecialApartmentStatement`.

The provenance is internal. The implemented proof uses the actual
integral-point image membership, the original quotient action, and the
published conjugate-apartment transport equality; it has no characteristic
restriction and uses no fixed-apartment or unramified-descent theorem as a
proof input.
