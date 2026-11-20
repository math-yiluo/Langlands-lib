# Normal immersed multiplicative-type subgroups are central

Worker 885, using Worker 5698's conjugation and relative rigidity constructions.

This module derives the normal-subgroup clause of the published
`MultiplicativeTypeFibrewiseCentralityStatement` from the actual relative
multiplicative-type rigidity and conjugation results. The theorem
`RelativeMultiplicativeType.isCentral_of_isNormal_of_connectedFibres` accepts
the clause's immersion, multiplicative-type, normality and connected-residue-fibre
hypotheses. It does not need the clause's local-finite-type hypothesis on the
ambient group.

`geometricallyConnected_of_connectedResidueFibres` applies the rational unit on
each residue fibre to obtain geometric connectedness of the ambient structure
morphism. An immersion is a monomorphism of schemes, and
`Over.mono_of_mono_left` makes the inclusion a monomorphism in the over-category.
The theorem `MultiplicativeTypeNormalCentral.isCentral_of_isNormal` then proves
centrality: conjugation is a natural multiplicative family of endomorphisms of
the subgroup, parametrized by the ambient group; relative multiplicative-type
rigidity identifies conjugation by every point with conjugation by the identity.

This is an internal derivation of SGA 3, Exposé IX, Corollaire 5.5 as encoded by
the unchanged published target. It uses the direct rigidity argument described
above, rather than the source's descent-of-central-homomorphisms route.
