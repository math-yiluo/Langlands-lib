# Base-change stability of central isogenies

This module proves the published proposition
`Langlands.GroupScheme.CentralIsogenyBaseChangeStatement` over arbitrary
schemes and arbitrary morphisms of bases.

The proof first establishes `IsCentral.baseChange`. The multiplicative
`baseChangePointsEquiv` transports the commutation relation to the old base.
Its compatibility with the group homomorphism and naturality in the test
scheme identify that relation with the original centrality hypothesis.
Every test scheme and every restriction remains quantified.

For `IsCentralIsogeny.baseChange`, the existing `IsIsogeny.baseChange`
preserves finiteness, flatness and surjectivity of the actual scheme
morphism. The usual morphism-property pullback theorem separately preserves
the explicit local finite presentation condition. Finally, the inverse of
the published `kernelBaseChangeIso` identifies the actual new kernel
inclusion with the pullback of the old kernel inclusion, by
`kernelBaseChangeIso_inv_ι`. Precomposition of the central pulled-back
inclusion with that inverse proves centrality of the full new kernel.

The final theorem `centralIsogenyBaseChange` has exactly the published
proposition as its type. This is an internal derived closure result for the
Library predicate and existing kernel comparison, following the provenance
and conventions documented in the statement module. It requires no
flatness of the change of base, reducedness of tests or kernels, field
hypothesis, or representing centre.
