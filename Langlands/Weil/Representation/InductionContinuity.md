# Usual-topology continuity of restriction and finite-index induction

Worker 17 authored this module. It proves that restriction and finite-index
induction preserve the usual-topology predicate `IsContinuous`. That predicate
asks for continuity of the action into complex endomorphisms with Mathlib's
module topology, which is the usual topology of a finite-dimensional complex
space. It is not the open-kernel convention. For that convention,
`InductionTopology` gives the induction theorems, and the two predicates stay
separate.

`isContinuous_restrict` shows that restriction along a continuous homomorphism
preserves continuity: the action of the restriction is the original action
composed with the homomorphism. `continuousRestrict` and
`continuousRestrictClass` give the operation on continuous objects and on
genuine isomorphism classes with the continuity condition.

`isContinuous_induce` proves that induction from an open finite-index subgroup
`S` of a topological group preserves continuity. The implemented proof runs as
follows. Fix the chosen right-coset representatives `q.out` from `Induction`.
`U` is the set of elements `g` with `q.out * g * q.out⁻¹ ∈ S` for every coset
`q`. It is an open neighbourhood of the identity because it is a finite
intersection of preimages of `S` under continuous maps. For `g` in `U`,
equivariance of induced functions gives
`f (q.out * g) = A (q.out * g * q.out⁻¹) (f q.out)`. So in the published coset
coordinates `Induction.coordinates`, the action of `g` is the block-diagonal
operator whose `q`-block is the action of that conjugate. Block-diagonal
assembly followed by conjugation by the coordinate equivalence is complex-linear
from a finite product of endomorphism spaces. All of these spaces carry module
topologies, so it is continuous. The conjugates depend continuously on `g` in
`U`. Hence the induced action is continuous on `U`, and so it is continuous at
the identity. Endomorphisms of a finite-dimensional complex space form a
topological ring for the module topology. Mathlib's
`continuous_of_continuousAt_one` therefore gives continuity of the homomorphism
everywhere.

`continuousInduce` and `continuousInduceClass` give the resulting operation on
continuous objects and on genuine classes with the continuity condition.
Equivalences come from the published `induceEquiv`. Irreducibility is not
claimed to be preserved.

`isContinuous_induceAlong` handles the `induceAlong` construction from
`Langlands.WeilDeligne.InductionAlong`, for an open embedding `ι : H →* G`
whose range has finite index. That construction restricts along the inverse of
the corestriction and then induces from the range. The published
`continuous_rangeInverse` and `isOpen_range` supply the continuity and openness
hypotheses of the two results above. `continuousInduceAlong` and
`continuousInduceAlongClass` give the operation on continuous objects and
classes. The intended local use is the extension map `W_E → W_F` of a finite
extension of p-adic fields, which is an open embedding with finite-index range.
That local specialization is not made here.

Provenance: this is derived infrastructure for Tate, *Number theoretic
background*, Corvallis Part II. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`. In §2
(printed page 9), a representation of a topological group is a continuous
homomorphism to `GL(V)` for a finite-dimensional complex `V`, and `M(G)` is the
set of their isomorphism classes. §2.1 (printed pages 9–10) uses restriction
and induction between `R(W_F)` and `R(W_E)`, identifying `W_E` with a closed
subgroup of finite index in `W_F`. By §1.4.5 (printed page 7), the subgroups
`W_E` are the open subgroups of finite index. Tate's induction map on
representations presupposes that induction from such a subgroup preserves
continuity, but he states no such lemma. This module proves it for an arbitrary
open finite-index subgroup of a topological group. The argument above is the
implemented route; it is not quoted from that source and adds no axiom.

Imports: the published `Langlands.Weil.Representation.InductionTopology` (and
through it `Induction` and `Predicates`) and `Langlands.WeilDeligne.InductionAlong`
(and through it `Restriction`). Pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` supplies `IsModuleTopology`, its
finite-product instance, `IsModuleTopology.continuous_of_linearMap`,
`IsModuleTopology.isTopologicalRing` and `continuous_of_continuousAt_one`.
Compilation alone does not establish independent semantic acceptance or
publication.
