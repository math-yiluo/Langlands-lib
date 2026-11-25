# Global subgroup conjugacy from a trivial difference cocycle

This internal construction descends a supplied local conjugator
using a trivial source-subgroup cocycle. It is derived from the Library's
all-test conjugating-point relation, monic cocycle lifting, and effective
fpqc descent of morphisms.

Let `i : B ⟶ G` and `i' : B' ⟶ G` be monomorphisms over any scheme `S`.
Suppose the full subgroup functor `range i` is self-normalizing. Supply a
quasi-compact, flat, surjective cover `U ⟶ S` and a point `g ∈ G(U)`
conjugating the two ranges on every refinement. The difference cocycle
`g(a)⁻¹ g(b)` lifts uniquely to `B`. If that actual lifted cocycle is
trivial, `IsConjugatingPoint.exists_base_of_isTrivial` proves existence
of a conjugating section in `G(S)`.

A primitive `f` of the lifted cocycle makes `g f` independent of the
cover point. Effective descent produces an actual section `s`. Right
multiplication by the `B`-valued primitive preserves conjugacy; fpqc
membership descent for the two represented subgroups then gives conjugacy
by `s` on all test schemes over `S`.

`globalConjugatingPoint` chooses this section and
`globalConjugatingPoint_spec` states the equality of represented ranges
after its actual inner automorphism. Triviality of the lifted cocycle,
self-normalization, and the initial cover and conjugator remain explicit
hypotheses. No reductivity, affineness or torus structure is assumed here.
This module does not assert that those hypotheses hold for any particular
subgroups. The intended use is the descent step in Conrad, *Reductive group
schemes* (2014), Proposition 6.2.11(2), pp.210–211; the implemented proof is
an internal composition of the imported descent constructions.
