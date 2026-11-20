# Real-place injectivity from the simply connected arithmetic kernel

`SimplyConnectedRealPlacesKernelReductionStatement` gives the real-place
injectivity clause from the Hasse kernel for simply connected groups on
finite Galois covers. The local comparison first gives cohomology at all
completions. Extend the field cover to a finite Galois cover and refine
both cocycles and all local cohomologies.

Over the Galois cover, take the inner twist of the group by the first
refined cocycle. The twisted group is simply connected by invariance
under isomorphism and reflection of field extension. The difference
cocycle of the second refined cocycle is locally trivial. The arithmetic
kernel theorem, supplied as the premise, makes the difference trivial.
This yields cohomology of the two refined cocycles. Fpqc reflection
returns the cochain on the original finite field cover.

This is the simply connected input used for injectivity in J. S. Milne,
*Algebraic Groups* (2017), Theorem 25.65, printed p. 563, with the
arithmetic Hasse input of Theorem 25.64, printed p. 562, taken in its
kernel form after an actual cocycle inner twist.
