# Torus rigidity of locally inner comparisons preserving the cocharacter

This internal construction uses the actual centralizer theorem for the
canonical positive-coroot cocharacter of a supplied affine pinned model.
Every relative conjugating point realizing an automorphism which fixes that
cocharacter has a unique lift to the coordinate torus. The construction
`torusConjugator` chooses this unique lift and recovers the original
conjugating point under the actual inclusion.

If the automorphism is fppf-locally inner, it fixes the whole coordinate torus
pointwise. On the pullback of the witness cover to any test scheme, both the
conjugator and a tested torus point belong to the same commutative torus.
Their commutation makes conjugation trivial. The cover projection is an
epimorphism, so the equality holds on the original test scheme.

Consequently, two inner-equivalent actual comparisons which preserve the
canonical cocharacters have identical restrictions to the entire source
coordinate torus. Apply the preceding argument to the source discrepancy,
then cancel the inverse of the second comparison.

These are derived consequences of cocharacter centralizers and commutativity,
with no affineness, connectedness or nonemptiness assumption on the common
scheme or its tests. This module does not yet show that the conjugator is
central in the whole group. Pinning rigidity and uniqueness of the full
comparison remain separate obligations.
