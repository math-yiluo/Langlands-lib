# Structural assembly of the closed common-Levi continuation target

The definition `commonLeviAssemblyData` bundles simultaneous common-Levi
presentations with their exact auxiliary opposite model. The result is a
dependent pair: its second component represents the dynamic parabolic of
the negative split-component cocharacter from its first component's second
presentation. This construction is purely structural and works over arbitrary
fields.

The accompanying internal theorem
`conditionalDynamicCommonLeviContinuation_of_presentationReduction`
discharges the structural assembly obligations of the actual common-Levi
continuation target. Its conclusion is the entire
`ConditionalDynamicCommonLeviContinuationStatement`, with independent field
and inducing-carrier universes. It retains exactly two proposition premises:
`DynamicCommonLeviPresentationReductionStatement` and
`ConditionalParabolicIntertwiningStatement`. They remain separate proof
obligations; this module does not establish the closed target without them.

The theorem introduces exactly the original target's data and constructs
`commonLeviAssemblyData`.
`DynamicCommonLeviPresentations.commonData` constructs simultaneous complete
root presentations on the literal common centralizer scheme, sharing one
split-component inclusion. Their Levi composites coincide by
`CommonData.levi_comp`; their geometric-radical and all-test realization
witnesses are fields of the constructed data. For the auxiliary cocharacter
specified in the presentation reduction, `oppositeData` constructs the
represented parabolic and geometric radical.
`parameterScheme_locallyOfFiniteType` supplies the inherited local finite-type
hypothesis for the canonical common Levi.

The proof then applies
`commonLeviContinuationExists_of_presentations`. That adapter constructs
the source point decompositions, closedness, projection continuity, finite
relative Weyl enumeration, and original compact-subgroup factorizations.
It concludes the required continuation existence with the original compact
open subgroup, inducing representation and factorization witnesses.

No splitness, characteristic, positive-rank or irreducibility assumption is
added. The auxiliary representation universe remains arbitrary. This is a
derived composition of the two structural adapters and the published
proposition interfaces, rather than an additional assertion from the
literature. The source analytic theorem represented by the second premise is
Waldspurger 2003, IV.1.1, registered as `waldspurger-2003-plancherel`.
