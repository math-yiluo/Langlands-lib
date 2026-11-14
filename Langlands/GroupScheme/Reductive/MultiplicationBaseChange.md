# Actual subgroup multiplication and base change

This is an internal compatibility deduction from the published product-points,
base-change-points and product-comparison interfaces. It applies to arbitrary
schemes and actual group homomorphisms whose values commute on all test schemes.
The commuting hypotheses before and after base change are explicit.

`prodHom_eq_commutingSubgroupMultiplicationHom` identifies the point-defined
product homomorphism with the actual commuting subgroup multiplication by their
actions on every test scheme. The two coordinate lemmas use the canonical
`baseChangeTensorIso` and its projection identities. `baseChange_prodHom` then
uses the group isomorphism `baseChangePointsEquiv` to compare both maps, expanding
the product formula and checking the two coordinates.

Finally `isCentralIsogeny_baseChange_prodHom_iff` transports the full central
isogeny predicate through this equality and the source product isomorphism.
It retains the actual scheme-theoretic kernel convention; it does not assert
that a multiplication map is a central isogeny without the displayed premise.

`MultiplicationBaseChangeStatement` packages the identification with actual
commuting multiplication, the base-change equality, and the central-isogeny
equivalence for every universe and every base morphism. The theorem
`multiplicationBaseChange` proves this conjunction with the three preceding
lemmas. Neither centrality nor closedness of the two input maps is required.
