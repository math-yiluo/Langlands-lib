# Conditional assembly of a common rational maximal torus

Worker 1329, with the geometric interface and assembly route supplied by
Worker 1349.

This is internal assembly infrastructure for the common rational maximal torus
problem. It derives conditional results from the existing actual group-scheme
predicates and named structural propositions. It supplies no proof of the
structural propositions.

`Langlands.CommGroupScheme.groupIso` turns an isomorphism of commutative
group schemes into the underlying isomorphism of group schemes. It uses
the same homomorphism and inverse, with the inverse laws obtained by
forgetting the additive notation on homomorphisms.

`MaximalTorusConjugacyStatement.maximalToriAreConjugate` specializes the universal
conjugacy proposition to one smooth affine connected group over an algebraically
closed field. It converts the supplied isomorphism of commutative group schemes
to its underlying group-scheme isomorphism, preserving the conjugacy equation.

`exists_isMaximalTorus_comp_of_geometric` concerns a closed homomorphism
`j : H ⟶ G` between smooth affine groups over any field `k : Type u`.
It assumes geometric connectedness of `H` and one maximal torus of `G` over
the algebraic closure that factors through the base change of `H`. Its three
other explicit hypotheses are `MaximalTorusExistenceStatement`,
`MaximalTorusBaseChangeStatement`, and `MaximalTorusConjugacyStatement`.
The conclusion is a torus and factor `f` over `k` for which `f ≫ j` is an
actual ambient maximal torus.

The proof chooses a rational maximal torus of `H` using the existence
hypothesis, extends its maximality to the algebraic closure using the
base-change hypothesis, and invokes geometric conjugacy inside `H` to
compare it with the given ambient maximal torus. The existing conditional
transport theorem promotes maximality in `H` to maximality in `G` over the
algebraic closure. The reverse implication of the base-change hypothesis
then reflects ambient maximality to `k`. Smoothness and affineness after
base change follow from their stability under scheme pullbacks.

`exists_common_isMaximalTorus_of_intersection` takes a torus mapping to the
actual pullback of two subgroup presentations, with maximal common composite
in the ambient group. Composing with the two pullback projections gives
the two required factors. Their composites agree by the pullback equation.
This last lemma needs neither parabolicity nor any structural theorem.

`parabolicIntersectionTorus_of_structural_inputs` combines the preceding
lemmas with `ParabolicIntersectionGeometryStatement`. This fourth explicit
structural hypothesis supplies smoothness, geometric connectedness and a
geometrically ambient maximal torus in the actual intersection. The common
map from the pullback to `G` is closed because both parabolic maps are closed.
Composing that closed immersion with the affine structure map of `G` proves
affineness of the intersection. The generic geometric-to-rational lemma
then applies, and the two projection factors give precisely the witnesses
required by the unchanged `ParabolicIntersectionTorusStatement`.
Connectedness of the original intersection is not needed: the existence
statement applies to smooth affine groups without that hypothesis.

These are derived categorical reductions. They do not establish rational
maximal-torus existence, preservation of maximality, geometric conjugacy,
or the smoothness, connectedness and full geometric rank of a parabolic
intersection. The final theorem is conditional on all four structural
propositions and is not an unconditional proof of the published
`ParabolicIntersectionTorusStatement`.

The imported `ExistenceStatement`, `MaximalBaseChangeStatement` and
`MaximalTransport` modules are due to Worker 1336; `SubgroupIntersection`
is due to Worker 308; and `ParabolicIntersectionGeometryStatement` is due
to Worker 1349. They are published dependencies. This contribution
imports them without changing their declarations or claiming their
structural propositions as proved.
