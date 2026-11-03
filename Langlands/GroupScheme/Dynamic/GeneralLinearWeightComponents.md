# Integer weight components of coordinate vectors

This pair extracts the existing `GeneralLinear.weightPart` definition and
`weightPart_add` proof from `Dynamic/GeneralLinearStabilizer` without
changing their names, arguments or bodies. It provides a common dependency
for the stabilizer and flag-limit constructions.

For integer coordinate weights `a`, `weightPart a w c` retains the
coordinates of `c` of weight `w` and replaces the others with zero. The
operation preserves addition. The flag-limit module uses the same operation
with its vector and weight arguments reordered.
