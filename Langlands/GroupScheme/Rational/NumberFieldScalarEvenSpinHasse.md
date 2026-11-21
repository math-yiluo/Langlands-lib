# Hasse kernel for ordinary even spin groups over number fields

`NumberFieldScalarEvenSpinHasseStatement` concerns an actual spin cover of a regular scalar quadratic form of dimension `2 * n` with `3 ≤ n` over a number field. The source is simply connected and covers the identity component of the isometry group by a central isogeny. A cocycle on any finite Galois cover of the number field that is trivial after pullback at every place is already trivial on that cover.

The semisimple orthogonal identity component is perfect, so its reduced-norm character vanishes. Its inclusion in the isometry group factors through the norm-one group. The norm-one group is connected, so its inclusion factors through the identity component. The two factorizations give inverse isomorphisms. The simply connected cover has two geometric kernel points by the split even orthogonal kernel calculation, and the isomorphism preserves the full kernel. The scalar Clifford Hasse theorem then applies to the same group and Galois cover.

The arithmetic route uses the spinor-norm exact sequence in Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99.
