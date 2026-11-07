# Pushing out a group extension along an equivariant kernel map

This is a derived group-theoretic construction for the local Weil class-map
proof. Given a homomorphism `q : W →* G`, a normalized section `s`, and a
homomorphism `r : q.ker →* A` to a commutative `G`-group that respects conjugation,
apply `r` to the factor set of `s`. Associativity gives the two-cocycle identity.
The kernel coordinate of an element `x` is `x * s(q(x))⁻¹`; applying `r` gives
the left coordinate of a homomorphism from `W` to the constructed cocycle
extension. Its projection is `q`, and its restriction to the kernel is exactly
`r` followed by the coefficient inclusion.

The results use no arithmetic claim or external literature: they follow from
the displayed group operations and the published `NormalizedTwoCocycle`
construction. In particular they do not identify the cohomology class of an
actual Weil group. A normalized section can be chosen from surjectivity of `q`.

Changing the normalized section changes the cocycle by the explicit cochain
`g ↦ r(s(g) * t(g)⁻¹)`, so its actual second cohomology class is independent
of the section. The quotient and coefficient group have a common universe,
while the group `W` may have a different universe.

When `W` is a topological group, `G` is discrete, and `q` and `r` are continuous,
the section is continuous and hence so is the kernel coordinate. The pushout
homomorphism is therefore continuous for the displayed product topology on
the cocycle extension. No topological extension classification is assumed.
