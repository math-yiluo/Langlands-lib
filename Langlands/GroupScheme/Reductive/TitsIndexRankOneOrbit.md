# The distinguished orbit of an actual rank-one Tits index

This internal helper constructs an actual distinguished vertex when
`splitRank G = 1`. For every field `k : Type u`, every affine, locally finite
type group scheme `G` over `k`, and every actual datum `d : TitsIndexData G`,
the distinguished vertices are exactly the full absolute Galois star orbit
of this chosen vertex. The datum supplies semisimplicity. No local-field,
simple-connectedness, absolute almost-simplicity or characteristic hypothesis
is needed.

## Provenance and proof

These are internal consequences of the published
`titsIndexSplitRank`, `titsIndexStarInvariant` and
`titsIndexRelativeSimpleRoots`, from
`Reductive/TitsIndexSplitRankProof` and `Reductive/TitsIndexStarProof`.
No new assertion from original literature is used.

`card_distinguishedOrbit_eq_one` specializes the published equality
`(Nat.card d.DistinguishedOrbit : ℕ∞) = splitRank G` to rank one and uses
injectivity of the natural-number inclusion into `ℕ∞`. The quotient therefore
has exactly one element. `exists_star_eq_of_rank_one` makes it a subsingleton,
equates the classes of any two distinguished vertices, and applies quotient
exactness. The defining relation of this quotient supplies an element of
`SeparableClosure k ≃ₐ[k] SeparableClosure k` taking the first vertex to the
second by the actual star action.

`rankOneDistinguishedVertex` chooses an element of the nonempty one-element
orbit quotient and then an actual representative of that class. Its value
lies in `d.distinguishedVertices`, so its root restriction is nonzero.
`mem_distinguishedVertices_iff_rankOne_orbit` characterizes the entire marked
set by the orbit of this representative. The forward implication uses
transitivity just proved. For the reverse implication, the published star
invariance of the zero vertices prevents a star translate of a distinguished
vertex from having zero restriction.

`rootRestriction_eq_of_rank_one` applies the published equivalence between
equal restrictions of distinguished simple roots and their lying in one star
orbit. Thus every distinguished root has the same actual restriction to the
chosen maximal split torus, which is nonzero by membership in the
distinguished set.

Finally, `distinguishedVertices_eq_singleton_of_star_trivial` assumes explicitly
that each element of the full absolute Galois group fixes every simple vertex.
The orbit characterization then reduces the distinguished set to the singleton
containing the chosen vertex.

## Scope

The construction is not canonical and the star action is never replaced by a
finite quotient. These results provide structural information for the local
rank-one enumeration. They do not classify the actual Cartan matrix, impose
division-algebra degree restrictions, exclude exceptional or trialitarian
indices, or prove `LocalRankOneTitsIndexStatement`. The unchanged unconditional
enumeration remains a separate proof obligation.
