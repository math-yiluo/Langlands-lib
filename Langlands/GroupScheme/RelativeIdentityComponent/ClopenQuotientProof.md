# Scheme quotient by a clopen relative identity component

`Langlands.GroupScheme.RelativeIdentityComponent.clopenQuotient.{u}`
proves the unchanged published `ClopenQuotientStatement.{u}`.
For any scheme `S`, smooth separated quasi-compact group scheme `G/S`,
and supplied relative identity component `i : H → G` whose inclusion is
closed, it constructs
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient i`.
It adds no affine, Noetherian, reductive or other hypotheses.

The proof applies the complete
`clopenQuotient_of_separatedEtaleScheme` reduction to
`AlgebraicSpace.separatedEtaleScheme`.
The latter supplies schemehood for a separated algebraic space with an
etale surjective scheme atlas whose structural map is etale. Its
paired proof describes the independent schemehood argument.

The reduction first constructs the canonical algebraic-space quotient
of the actual right-coset relation `G ×ₛ H`. Openness of the supplied
identity-component inclusion and smoothness of `G/S` make `H/S`
smooth. The relation is the base change of `i` under right difference,
so it is open and closed in `G ×ₛ G`. These properties descend along
the smooth surjective presentation to the space diagonal. The space is
therefore separated and has an etale-over-base scheme atlas. Applying
the general schemehood theorem gives the quotient scheme.

The resulting scheme is separated, locally of finite type and
quasi-compact over `S`. Its projection from `G` is smooth, surjective
and quasi-compact. The represented kernel pair is the original actual
coset relation; consequently, on every test scheme over `S`, two
points have the same quotient image exactly when their right
difference factors through `i`. The all-test criterion includes
nonreduced and nonaffine tests. These are precisely the fields of the
published conclusion.

This implements the representability step in Conrad,
*Reductive group schemes* (2014), Proposition 3.1.3, pp.82–83,
by the arbitrary-base separated etale space criterion. The full
schemehood criterion is the etale specialization of Stacks Project
Proposition 67.50.2, Tag 03XX. The proof retains the original target and
its imports unchanged.
