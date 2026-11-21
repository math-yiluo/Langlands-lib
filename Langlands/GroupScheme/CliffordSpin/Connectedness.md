# Connectedness of the scalar Clifford lift group

`ScalarCliffordConnectednessStatement` concerns the affine Clifford model of a regular scalar quadratic form in characteristic zero. In dimension at least two, connectedness of the norm-one isometry group implies connectedness of the Clifford lift group. `connectedSpace_groupScheme_of_connected` proves this, and `isSemisimple_groupScheme` deduces semisimplicity when the target norm-one group is semisimple.

The central isogeny restricted to the identity component of the Clifford group remains surjective onto the connected target. Over any algebraically closed coefficient field, each lift therefore differs from one in the identity component by a scalar kernel point. For each such scalar, the Laurent family specializes to the identity at one and to that scalar at the corresponding root of unity. The spectrum of the Laurent algebra is connected, so its entire image factors through the identity component. The identity component thus contains all algebraically closed field points and its inclusion is surjective. Cartier smoothness and the central isogeny give semisimplicity when the target is semisimple.

This is a derived geometric comparison for the actual Clifford covering used in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99.
