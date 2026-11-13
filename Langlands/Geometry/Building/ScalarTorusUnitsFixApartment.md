# Scalar torus units fix the ambient apartment

Author: Worker 229.

The Prop-valued `KPApartmentData.ScalarTorusUnitsFixApartmentStatement` states
the assertion uniformly in the source map and unit-kernel point, for fixed
`v`, `D` and `C`. The theorem `KPApartmentData.scalarTorusUnitsFixApartment`
proves this proposition.

The theorem `KPApartmentData.map_torusUnits_smul_apartmentMap` works over any field
with an integer-valued valuation. For full V6-compatible apartment data `D` of a
torus `T`, a map `f : S → T`, and a point `t` in the common character-valuation
kernel of `S`, the image of `t` in the ambient group fixes `D.apartmentMap x` for
every `x` in the original apartment. No splitness of `S` is required.

This is an internal consequence of the published integer-valuation centralizer
adapters. Map `t` along `f` and the supplied factorization `C.s : T → C.Z`.
Functoriality of the common character kernel puts this point in the kernel of
`C.Z`. Full V6 makes its image fix the apartment. The equation `C.s ≫ C.j = iT`
identifies that image with the image of `t` in the stated conclusion.
