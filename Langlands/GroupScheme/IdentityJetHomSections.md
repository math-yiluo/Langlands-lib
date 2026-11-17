# Actual identity-jet sections under group homomorphisms

This internal construction transports actual affine augmentation quotients
through group homomorphisms over a common base. It uses the identity-section
naturality and actual jet section comparisons in the imported modules.

For a homomorphism `f : H → G` and an open `U` of their common base,
`homGroupSections f U` is pullback of actual group functions over `U`.
It respects the actual `Γ(S,U)` scalar action and commutes with evaluation
at the identity. Thus the pullback maps every power of the augmentation
ideal into the same power for `H`. `homQuotientSections f n U` is the
resulting map of augmentation-power quotient algebras. Identity and
composition laws hold and its formula on quotient classes is pullback
of the original group functions.

When both group structure morphisms are affine, `homSections f n U`
transports this map through `IdentityJet.sectionsEquiv` to an actual
linear map between sections of the actual identity neighborhoods.
The groups need not be smooth and the base is arbitrary.

`homSections_quotientMap` computes this map on the actual restrictions of
group functions: it is the restriction to the jet of their actual pullback
along `f`. The identity and composition laws transport from the quotient
algebras. `isoSections e n U` uses the maps of an actual group isomorphism
and its inverse to give a linear equivalence of actual affine jet sections.

For an actual map `j : G.total → Spec B` and an ideal `I` vanishing on
the identity, `vanishesAtIdentity_hom` proves the corresponding vanishing
for `f ≫ j`. The theorem `homSections_restrict_quotientCoordinates` says
that pulling back the restricted global quotient-coordinate sections
agrees with the quotient-coordinate sections of the composite actual map.
The proof compares both sides in the actual affine augmentation quotient,
reduces to a representative in `B`, and applies composition of function
pullback. No assumption on the smoothness of either group is used.

This constructs and compares the actual section modules on affine opens.
An arbitrary change of the base scheme and comparison with a Grassmannian
classification kernel are separate obligations.
