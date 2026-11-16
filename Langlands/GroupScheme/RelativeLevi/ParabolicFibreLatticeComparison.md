# Comparing the lattices on two field fibres of a split group

This internal construction derives a `ParabolicRootLatticeComparison` from a
supplied `IsFibrewiseRootDatumOf`. It compares any two supplied field algebras of
the base ring, without a map between those fields. The additive equivalences
identify both full lattices by the fixed integer exponent coordinates.

The root-membership condition follows from `IsFibrewiseRootDatumOf.mem_roots_iff`
on each fibre. The pairing condition follows from the integer dot-product formula
for exponent characters and cocharacters. The final identity says that the
comparison carries each exponent cocharacter to the same exponent cocharacter on
the other field. This is derived from the coordinate equivalences and adds no
existence claim for a split torus or a root datum.
