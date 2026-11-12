# Actual affine root groups under Levi projection

This internal comparison uses the actual same-torus cocharacter-Levi data constructed in `LeviApartmentRestriction` and the surjective affine projection of `LeviApartmentProjection`. It defines `leviAffineRootPullback` by precomposition with that projection. The ambient and Levi groups, their original closed inclusion, and the full valuation functions are retained.

The finite filtration images follow from the literal root-valuation restriction. Evaluating an affine root group at any apartment point gives the ordinary affine root-group image; taking the directed supremum over every positive real shift gives the strict group image. The actual root support of the Levi is the ambient support with zero cocharacter pairing. Doubling preserves this zero pairing, so the doubled-root subgroup has exactly its original ambient image, with the trivial-group convention retained if the double is not a root. Injectivity of the closed inclusion reflects the product-containment test in the definition of ordinary affine roots. The ordinary and extended affine roots of the Levi therefore pull back to ambient roots of the same kind.

The last comparison constructs the descended functional for any ambient functional whose derivative is a Levi root: it has the same value at the chosen projected point and the same derivative after pullback, so affine extensionality proves the identity.

These are derived consequences of the published constructions, supporting the root comparison in KP Section 6.7.2. This unit asserts neither the full affine-root-system axioms for the Levi nor specialness, vertexhood, compact-preimage equality, parabolic factorization or the simultaneous basis.
