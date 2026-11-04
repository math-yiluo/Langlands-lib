# Connectedness and actual irreducible-component incidence

This derived construction isolates the finite incidence argument used in
Stacks Project, Lemma 37.28.4 (tag 055G), proof, final paragraph. That argument
supports the generic-constancy prerequisite for Conrad's *Weil and
Grothendieck approaches to adelic points*, Theorem 3.4(2), printed pages 5–6.
The registered Stacks snapshot is
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
This module proves the incidence comparison; it does not prove geometric
generic constancy or any spreading assertion.

For an actual family of subsets `s`, `intersectionRelation s i j` means
that `s i` and `s j` have nonempty intersection. It permits equal indices.
`IntersectionChainConnected s` requires an index and a finite chain of
such intersections between every two indices. Nonemptiness is explicit,
so an empty family is not connected in this sense.

The module proves that a finite family of nonempty closed subsets whose
union is connected has a connected intersection relation. For a fixed
index, take the indices reachable by a finite chain. Their sets and the
remaining sets give two closed unions. If an index were unreachable,
both unions would be nonempty. The closed-set characterization of
preconnectedness would force an intersection, extending a chain into
the unreachable set and giving a contradiction. Individual connectedness
of the closed subsets is unnecessary for this direction.

Conversely, for a family of connected sets, connected incidence makes
the union connected, by Mathlib's existing
`IsConnected.iUnion_of_reflTransGen`. This direction does not require
closedness or finiteness. The displayed equivalence retains both hypotheses
for the combined finite closed-cover comparison. A bijection of indices
preserving pairwise nonempty intersections preserves chain connectedness,
by transporting each step in a finite chain.

`componentSets A` is the family of actual elements of
`irreducibleComponents A`, with each component its original subset of A.
`irreducibleComponentIncidence A` is their actual intersection relation.
`IrreducibleComponentChainsConnected A` is the chain condition on that
family. These use Mathlib's maximal irreducible subsets, not a supplied
list of putative components.

The components are closed, nonempty and connected and cover the space.
Thus, when the space has finitely many irreducible components,
`connectedSpace_iff_componentChains` identifies ordinary `ConnectedSpace`
with the component chain condition. This includes the empty space, for
which both sides are false. No separation or sobriety hypothesis is used.
The module specializes this to every Noetherian topological space and
proves that a bijection of actual finite component families preserving
intersections preserves connectedness of the ambient spaces.

Finally, `geometricallyConnected_iff_componentChains` applies the comparison
to every actual field base change of an arbitrary finite-type scheme
morphism. Local finite type and quasi-compactness are the only morphism
hypotheses. Each field base change has Noetherian source, and Mathlib's
definition of geometric connectedness tests exactly these pullbacks.
The two schemes have a common arbitrary universe. They need not be affine,
separated, proper, smooth, flat or Noetherian. There is no restriction to
separable extensions or perfect fields.

The last result is a reformulation, not a proof that the incidence patterns
are constant in families. Finite étale splitting, spreading geometric
irreducibility, preservation of intersections after shrinking, and the
unconditional generic-constancy and constructibility targets remain open.
