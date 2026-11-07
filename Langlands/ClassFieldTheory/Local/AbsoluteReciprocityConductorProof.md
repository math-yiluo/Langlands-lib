# Absolute reciprocity and conductors

This internal helper derives the two conductor clauses of
`AbsoluteUpperReciprocityTheorems` from the explicit hypothesis
`AbsoluteReciprocityRealUnitImages`. It does not assert that hypothesis.
All fields and topological realizations remain universe polymorphic. Every
continuous complex quasicharacter is allowed, without a finite-image condition.

`reciprocityUnitLevelEquiv` is the actual restriction of the reciprocity map to
`U^(ceil v)` with codomain the absolute abelian upper group. The published
`profiniteReciprocityCompletion` proves injectivity for every map satisfying
the geometric reciprocity relation. The supplied real-image equality then
identifies the range, giving a multiplicative equivalence. Its coercion lemma
states that it evaluates to the original reciprocity map.

For the conductor-level criterion, the all-level unit comparison rewrites the
least-level conductor bound as `U^n ≤ ker χ`. Injectivity of reciprocity makes
this equivalent to containment of the two actual images. The explicit
real-image hypothesis supplies the required absolute upper group.

For the last-break criterion, the conductor is a natural number. If it is
`n + 1`, it exceeds `n`, and every real `v > n` has `ceil v ≥ n + 1`.
Conversely nontriviality at level `n` forces the conductor above `n`, and
triviality at the later real level `n + 1` bounds it by `n + 1`. This also
covers `n = 0`. The combined theorem packages exactly the two published
conductor propositions, retaining the real-image hypothesis visibly.

Provenance is internal: the unit-filtration comparison, the published
profinite completion theorem, injective subgroup image transport, and
natural-ceiling arithmetic suffice. This module proves no new arithmetic
finite-image or ramification theorem.
