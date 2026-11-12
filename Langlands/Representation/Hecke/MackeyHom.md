# The Hom Mackey natural isomorphism

This supporting unit proves the first isomorphism of Renard III.2.11 Theorem
(printed pp.82–83 / PDF pp.88–89), using the actual transported Hecke functor.
It does not assert the second, conditional tensor isomorphism.

For a right adjoint `R` of continuous pullback, `homMackeyEquiv` follows exactly
(III.2.11.1)–(III.2.11.5). It uncurries a map into smooth Hom, uses the pullback
adjunction backwards, identifies the restricted tensor with the tensor of the
restricted representations, curries over H, then uses the adjunction forwards.
Each step is natural in the testing object, contravariantly in V, and in W.
The parameter-natural representability constructor therefore assembles an
isomorphism on the full product category, not just objectwise comparisons.

`heckeHomMackeyIso` specializes this construction to the original transported
Hecke right induction, taking its III.2.1 adjunction as an argument and using the
published natural comparison between continuous pullback and transported Hecke
forgetting. The required adjunction is supplied by the published theorem
`smoothInductionAdjunctionStatement`; this supporting definition does not yet
assemble the full target statement.
All group and carrier universe parameters remain independent.
