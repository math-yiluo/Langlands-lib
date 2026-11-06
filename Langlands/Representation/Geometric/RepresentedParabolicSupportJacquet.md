# Jacquet comparison for actual represented support quotients

This internal construction connects the original support-image filtration
with normalized target-radical coinvariants of the compact stabilizer orbit
pieces. It implements the exactness and orbit-support steps of Renard,
*Représentations des groupes réductifs p-adiques*, 2026 version, VI.5.1,
printed pp.163–164 / PDF pp.169–170, together with the stabilizer
identification on printed p.171 / PDF p.177.

`leviInductionCoinvariantsRestrictionIso` specializes the same-vector-class
parabolic/ambient coinvariant comparison to actual normalized induction.
It identifies coinvariants of the restricted induced representation with
the published `leviJacquetInductionFunctor`.

`leviJacquetImage_eq_isoTransport_exactImage` checks the actual support
subspaces under this comparison. Applying the parabolic coinvariant
functor to a support inclusion and taking its image, then transporting
along this natural isomorphism, gives exactly the original ambient
`leviJacquetImageSubfunctor`. The proof lifts a quotient representative,
uses the comparison's same-vector-class formula and retains the original
support membership witness. It proves equality of actual subfunctors.

`leviJacquetImageQuotientIso` assumes compact containment for the target
radical as a subgroup of the target parabolic. The published exact
image-quotient comparison then identifies the quotient of two nested
ambient support images with normalized parabolic coinvariants of the
original support quotient. The construction composes the natural
quotient comparison with transport along the ambient isomorphism.

`leviJacquetSupportGradedIso` applies this result at each unchanged index
of the original support filtration. `leviJacquetSupportOrbitIso` further
assumes compactness of the source parabolic quotient and ambient
Hausdorffness and sigma compactness. It composes the previous comparison
with the pre-Jacquet support-orbit isomorphism to obtain normalized
coinvariants of the compact stabilizer orbit piece.

Every comparison is natural on the full smooth source category, with
independent field and carrier universes. The ordered-orbit convention,
the inducing half character, target inverse half character and original
quotient maps are retained.

This module does not derive the explicit compact-containment or source
quotient-compactness premises from the represented group hypotheses.
It does not compare the resulting orbit coinvariants with
`GeometricLemmaIntersectionDatum.pieceFunctor`. That local normalized
comparison, including the balance of moduli from distinct radicals,
remains a separate obligation. The full published geometric-lemma
statement is unchanged.
