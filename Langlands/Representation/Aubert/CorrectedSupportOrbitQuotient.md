# Actual corrected support quotients and orbit restriction

This internal construction identifies the actual corrected support quotients
with the actual compactly induced orbit pieces, and then takes their normalized
Jacquet modules. It uses the corrected single-orbit geometry and the proved
restriction-and-extension construction for arbitrary open support pairs.

For a general open orbit support pair with compact ambient inducing quotient,
`OpenOrbitSupportPair.compactSmoothQuotientIso` first identifies the raw
quotients; `OpenOrbitSupportPair.smoothQuotientIso` transports the compact-support quotient
isomorphism through the canonical compact-to-smooth inclusion. The latter is
an isomorphism because the ambient quotient is compact, and it preserves the
underlying function on each support. It therefore identifies the exact lower
submodule inside the upper one. The resulting isomorphism is natural on the
full category of smooth complex covariance representations. Its formula on
every quotient representative is restriction along `q ↦ w⁻¹ q`.

For supplied p-adic data, `correctedInductionOrbitIso` precomposes this
construction with the actual smooth inducing covariance functor, including
the positive half-modulus character. Both corrected Weyl supports are required
to be length-upper tails, and the removed Weyl element must belong to the
corrected core. The concrete support pair proves the actual single-orbit
difference, openness, containment and target-parabolic invariance.
Compactness of the actual parabolic quotient supplies the compact-to-smooth
comparison in all natural ranks, including zero. The displayed evaluation
formula uses the inverse permutation matrix, as in the published orbit
convention, and retains the same actual inducing function.

`correctedJacquetOrbitIso` composes this identification with the proved
comparison between the quotient of actual Jacquet support images and the
normalized coinvariants of the support quotient. Thus its source consists of
the actual image subspaces of normalized Jacquet applied to actual normalized
induction; its target is `parabolicOrbitJacquetFunctor`, with the existing
inverse half-modulus normalization at the target.

The provenance is internal: canonical compact-to-smooth transport, actual
orbit restriction with its proved extension theorem, concrete corrected
single-orbit geometry, and exact normalized coinvariants. No compatibility
between different source block shapes, orbital integral across different
orbits, exterior-sign identity, concentration or effectivity is asserted here.
