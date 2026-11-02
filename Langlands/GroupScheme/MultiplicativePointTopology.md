# Actual multiplicative coefficient points and units

For a commutative base ring `R` and a coefficient algebra `A` in the same
universe, `affineUnitsEquiv` is the existing `Gm.affinePointsEquiv` on the
actual scheme-point carrier `GroupScheme.affinePoints A`. No point carrier
or group operation is changed.

`universalUnit` is the global unit represented by the identity point of the
actual multiplicative group. Naturality of the existing represented-units
comparison proves `affineUnitsEquiv_eq_map`: the coefficient unit is the
image of this global unit under regular-function evaluation at that point.
The general coefficient-evaluation identity then proves
`affineUnitsEquiv_naturality` for every coefficient algebra homomorphism.

If `A` has a topology, the regular-evaluation topology on the point carrier
makes both the value of the universal unit and the value of its inverse
continuous. The continuity criterion for the units topology therefore proves
`continuous_affineUnitsEquiv`. Neither a topology on `R` nor continuity of
ring operations on `A` is required for this direction. `affineUnits` records
the resulting continuous monoid homomorphism.

This is an internal construction from the published actual multiplicative
group and its represented-units naturality, together with the regular-function
topology of Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Section 2.2, Theorem 2.2.1 and equation (2.8), printed pages 51–53. The
implemented proof uses the universal global unit, rather than a chosen Laurent
presentation. Inverse continuity and a multiplicative homeomorphism are not
asserted here.

The universal-unit calculation unfolds the shared affine-point carrier when
rewriting naturality; the coefficient point and its associated unit are unchanged.
