# Coefficient-stable ordinary chambers under apartment class comparison

Worker 352. This is derived interface content for the existing actual valuation
apartments. No new existence assertion is assumed or proved here.

`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus_of_centralizers`
combines `IsOmegaCompatible.changeCentralizer` from
`IntegerCentralizerRepresentative` with
`IsOmegaCompatible.eq_of_isMaximalSplitTorus` from
`IntegerOmegaApartmentUniqueness`. It identifies any two full-V6-compatible
integer valuation classes for the same actual maximal split torus of a connected
reductive group, even if their centralizer data use different representatives.
The field is arbitrary; neither a topology nor a local-field hypothesis is used.

The remaining theorems concern an arbitrary field extension `K/k`, a commutative
`k`-group scheme `T`, its homomorphism `i` to an affine `k`-group scheme `G`, and
two coefficient-stable actual KP apartments `D` and `E` for `i_K` whose complete
valuation carriers agree. They use the published affine equivalence
`apartmentAffineEquivOfCarrierEq`, which retains each root-valuation family.
This equivalence commutes with every actual affine coefficient automorphism.
The published complete affine-root comparison then identifies entire sign
facets and preserves and reflects ordinary regularity. Injectivity of the
equivalence on sets identifies setwise invariance of each ordinary facet.
`galoisStableChamberEquivOfCarrierEq` is the resulting equivalence between the
types of coefficient-stable ordinary chambers, sending a chamber to its actual
affine image. `exists_regular_galois_stable_facet_iff_of_carrier_eq` identifies
existence of a stable ordinary chamber in the two supplied apartments, with
their original coefficient actions and with no fixed-point hypothesis.

For a canonical class and an independently supplied class on the same torus,
the first theorem supplies carrier equality when both classes satisfy full
integer-valued V 6. These comparison results do not construct a canonical class,
a coefficient-fixed point, a residual minimal parabolic, or a regular invariant
facet. They do not transfer a chamber to a different torus.
