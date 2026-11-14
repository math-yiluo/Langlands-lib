# Relative Borels from the canonical sum of positive coroots

Author: Worker 693.

This internal unit chooses a canonical exponent for the actual affine
relative Borel construction and proves its functoriality under based
root-datum equivalences.

`BasedBorelExponent.positiveCorootSum` is the sum of the coroots positive for
the supplied dual base of a finite root datum. For a reduced datum, every root
pairs with it as twice its height in the original base
(`pairing_root_positiveCorootSum`), by expanding the root in simple roots and
applying the published positive-root-sum pairing formula to the flipped datum.
The perfect pairing supplies torsion-free lattice instances needed for
reducedness of the flipped datum. The sum is therefore regular on every root.
Neither the roots nor the coroots need to span the full lattices.

`coroot_height_eq` proves preservation of heights in the dual bases under a
root-datum equivalence matching their simple-root supports. It transports an
integral simple-coroot expansion through the contravariant coweight map.
`positiveCorootSum_coweightMap` reindexes the finite sum using that height
identity and the equivalence's actual coroot formula. It proves equality of
the actual lattice elements, not only agreement of their root signs.

For a reductive group over `Spec R` with a closed coordinate split torus
maximal on every residue fibre, a full fibrewise coordinate root datum and a
supplied base, `isRelativeBorel_positiveCorootSum` proves that the actual
dynamic parabolic associated to this exponent is relative Borel. At a supplied
field-valued fibre, the root-datum pairing is the coordinate dot product, so
regularity follows from the preceding pure root-datum theorem. Apply the
existing field Borel construction on each residue field and dynamic subgroup
smoothness over the original ring.

This argument also covers the zero ring: it constructs the dynamic group
over the original base and proves the fibre conditions point by point,
without first assuming a field-valued point exists.

`IsFibrewiseRootDatumOf.relativeQuasiSplitTorusDataOfBase` records this
relative Borel, the original closed fibrewise maximal coordinate torus and
its proved containment. The unit does not construct invariant group data,
effective descent solutions, or an innerness witness.
