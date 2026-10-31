# Coefficient quotients for the actual parabolic orbit

This internal prerequisite identifies the actual inducing coefficient quotient
in the parabolic-orbit calculation. It does not assert the normalized orbit
comparison, integration, Haar correction, or a natural isomorphism of the final
functors.

The subgroup `parabolicOrbitCoefficientRadical` is the intersection of the
orbit stabilizer with the target radical, viewed inside the stabilizer.
Switching the order of the subgroup inclusions gives a group equivalence with
`parabolicOrbitRadicalIntersection`. The explicit surjection and section from
`ParabolicOrbitComparisonData` prove that its image under inverse conjugation
and the source Levi projection is exactly `sourceUnipotent`.

For an arbitrary complex representation of the source Levi and a character
trivial on that source intersection radical, `parabolicOrbitCoefficientEquiv`
identifies the twisted, conjugated coefficient coinvariants with the source
intersection coinvariants. The construction composes the published
`Jacquet.coinvariantsMapEquiv`, transport along the proved image equality, and
`Jacquet.twistCoinvariantsLinearEquiv`. Both maps preserve coefficient
representatives. The identification is natural for every source coefficient
intertwiner, with independent universes for its two carrier modules.

The target intersection Levi has an actual section into the stabilizer.
Its image under the source coefficient map is exactly the inverse-conjugated
source intersection Levi element. The source intersection Levi normalizes the
source intersection radical. The quotient equivalence therefore also
intertwines the actual section action with inverse-conjugation transport of
the source Jacquet action, twisted by the restricted source character.

For every actual finite p-adic extension with its supplied compatible data,
the original positive induction half modulus is trivial on the source radical
intersection. This follows from the supplied unipotent refinement equality and
the published triviality of the outer half modulus on the refined radical.
`parabolicOrbitRefinedCoefficientEquiv` consequently identifies the actual
coefficient quotient with the genuine refined Jacquet carrier. Its inverse also
preserves representatives, and the identification commutes with every normalized
refined Jacquet map. The section-action formula on each coefficient class retains
exactly the source positive half modulus and inverse-conjugated source action.
No smoothness,
admissibility, dimension or length restriction enters this algebraic step.

The provenance is internal: this is a specialization and composition of the
named published quotient constructions and the explicit orbit subgroup maps.
Bernstein–Zelevinsky (1977), sections 5.16–5.17 and 6.4, motivate this step;
the integration and normalization assertions in those passages remain
separate proof obligations.
