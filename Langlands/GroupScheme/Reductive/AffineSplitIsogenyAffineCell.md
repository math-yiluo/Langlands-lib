# Powered cell compatibility over arbitrary affine bases

This internal supporting module removes locality of the original coefficient
ring from the actual powered cell-compatibility theorem. The source and
target retain genuine normalized simple-root data, affine structure
morphisms and closed coordinate tori. Corresponding simple supports and
positive systems, transported source words, a height-monotone source
positive-root enumeration, and the original characteristic condition are
supplied. The original ring may have nilpotents or be the zero ring.

The generic `cellCompatible_of_localBaseChange` checks compatibility
after scalar extension to every commutative local algebra. A local-ring
point of the original base defines such an algebra. The published
`liftCellPoint` keeps all additive and torus coordinates, and its
evaluation theorem identifies the two cell-map values through the
canonical point-group base-change equivalence. The local compatibility
identity therefore transfers to the original cell points. The published
affine-target local-ring equality criterion gives compatibility on every
scheme test.

For the actual powered family, normal simple-root data pull back with
the same integral root data, bases and words. The original characteristic
condition pulls back to each algebra. Exact root-power, Weyl-family and
torus-map base-change identities identify the scalar-extended original
cells with the two cells of the proved local theorem. Applying that
theorem discharges every local compatibility premise.

`PoweredAffineCellCompatibilityStatement` records the full arbitrary-ring
result, and `poweredAffineCellCompatibility` proves it in every universe.
This proves cell multiplication compatibility over the arbitrary
original affine base. Constructing normalized data from the free root
spaces and extending the compatible cell to the final ambient isogeny
remain separate obligations.
