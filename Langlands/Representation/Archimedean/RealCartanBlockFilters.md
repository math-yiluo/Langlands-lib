# Group the compact sign and low-mode projections by original blocks

The original sign projections commute because their diagonal reflections commute. The rotation projections commute on disjoint pairs, and each commutes with the sign projections supported outside its pair. These facts follow from the rotation coefficient formula and the published disjoint matrix identities.

The position and slot permutations of the ordered block layout turn the separate lists of signs and low projections into products of the corresponding block operations. Induction on the block list moves each sign operation across the later rotation operations and leaves the sign-before-low order within each induced block. This is the internal regrouping needed to apply the individual weighted Haar formulas to the actual compact trace.
