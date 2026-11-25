# Actual relative Borels through a coordinate split maximal torus

This internal construction works over an arbitrary commutative ring `R`.
It takes a reductive group, a closed coordinate split torus maximal on every
residue-field fibre, and a common full coordinate root datum on every
field-valued fibre. It constructs an actual relative Borel containing that
specified torus over `Spec R`.

`CoordinateRootDatum.exists_regularExponent` uses the integral functional
existence lemma for the flipped root datum to find a linear functional nonzero
on every root. Evaluation on the coordinate basis writes this functional as an
integer dot product. `regularExponent` selects its integer coefficient vector.
This choice depends on the root datum, not on a point or field.

`AffineRegularBorel.cocharacter` realizes any supplied integer exponent vector
as an actual cocharacter in the ambient group. Its dynamic parabolic is the
actual group `borel` with actual map `inclusion`. The coordinate torus
centralizes its own cocharacters, so it lies in this dynamic parabolic on every
test scheme (`torus_range_le`).

For an exponent vector nonorthogonal to every root of the common datum,
`isRegular_field` proves regularity on every specified field-valued fibre:
the root-datum hypothesis identifies all actual roots with the coordinate
root characters, and the character/cocharacter pairing is the integer dot
product. `cocharacter_baseChange` retains these exponents through the actual
split-torus base-change comparison.

`isBorel_field` applies the published regular-cocharacter Borel theorem to
each connected reductive field fibre. The actual dynamic inclusion remains a
closed representative of the correct dynamic subgroup. Applying the same
argument to the algebraic closure and comparing successive pullbacks gives
`isGeometricBorel_field`.

`isRelativeBorel` uses the published smoothness theorem for dynamic subgroups
over arbitrary rings, affineness and monicity of the actual closed dynamic
inclusion, and the geometric Borel result at every residue field.

`IsFibrewiseRootDatumOf.relativeQuasiSplitTorusData` chooses the regular
exponent and records the resulting actual Borel, the original coordinate
torus, its supplied closed fibrewise-maximal inclusion, and the proved
containment as `RelativeQuasiSplitTorusData`.

The construction does not choose a prescribed positive root system or pinning.
It does not construct a common fibrewise root datum, an invariant descent
cocycle or an innerness witness. Its provenance is an internal derivation from
the published root-datum, fixed-exponent, dynamic subgroup and field Borel
interfaces.
