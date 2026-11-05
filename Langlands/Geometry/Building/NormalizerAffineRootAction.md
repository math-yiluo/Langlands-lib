# Actual normalizer action on affine roots without AS 5

This is an internal construction from the published actual normalizer conjugation
of weak and strict affine root groups. It restricts the existing apartment action
to the subgroup preserving the ordinary affine roots. No apartment-axiom predicate
is used for that restriction. The final normalizer-image theorem remains open.

The proof transports the derivative of a functional through the quotient defining
the translation space. Actual normalizer conjugation also transports the double-root
subgroup, including its trivial value when the doubled character is not a root.
Injectivity and multiplicativity of conjugation then preserve the noncontainment
test defining an ordinary affine root. Applying the inverse normalizer point gives
the membership equivalence and the homomorphism `normalizerAffineRootAction`.

For `ValuationBuildingData`, the actual affine reflection action of any supplied
opposite factor pair and the root-preserving action prove that its integral coroot
is a coroot for the ordinary affine roots. If these roots form an affine root
system admitting rank zero (`IsAffineRootSystemWithRankZero`), uniqueness of coroots identifies it with any supplied system coroot. If
actual opposite factor pairs exist, each affine Weyl generator therefore has a
representative in the actual reflection-generated normalizer. This proves the
lower inclusion in the full normalizer image with only the explicit affine-root-
system and opposite-pair existence hypotheses. It does not prove existence of
opposite pairs, the affine-root-system assertion, facet fixing, or an upper
inclusion in the affine Weyl group.

All fields and algebraic groups are in arbitrary universe `u`. The first part
applies to any field and any `KPApartmentData`; the second part retains the actual
local-field and valuation-building data. No additional literature assertion is
claimed. The proof composes `RootReflectionConjugation`,
`ApartmentRootReflections`, the definitions of the actual affine roots and
`reflectionNormalizer`, and the published affine-root-system coroot uniqueness.
