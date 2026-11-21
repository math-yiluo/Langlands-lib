# Existence of an inertia type of finite period in a representation

`exists_pos_conj_eq` assumes that the inertia image of a representation `σ` of a
split group is a finite set. Then some positive power `lift ^ k` satisfies
`σ(lift^k n lift^{-k}) = σ(n)` for all inertia elements `n`. Conjugation by `σ(lift)`
permutes the finite image. The order `k` of this permutation works, by induction on
the iterates.

`exists_occurring_type` assumes that `σ` is a nonzero continuous finite-dimensional
representation with finite inertia image. It produces an inertia type `B` (continuous
and irreducible) with a nonzero inertia intertwiner `σ|_inertia → B`, whose class has
positive minimal period under Frobenius conjugation.

- `B` is the quotient of `σ|_inertia` by a coatom of its lattice of
  subrepresentations. The coatom exists because this lattice embeds in the
  Noetherian lattice of subspaces.
- `B` is irreducible by the Library's coatom criterion, and continuous as a quotient
  of a continuous representation.
- The quotient map is nonzero.
- By `exists_pos_conj_eq`, conjugation by `lift ^ k` fixes the class of `B`, so the
  class is periodic.

For local Weil groups the finiteness hypothesis holds for every continuous
representation (Library: `continuousWeilFiniteInertiaImage`). This module is internal
infrastructure for the proof of Henniart (1988), Proposition 2.2.
