# Assembling pair conjugacy from a Borel conjugator

This internal derived lemma combines a supplied rational conjugator
for two Borel subgroup ranges with the published rational conjugacy of maximal
tori in smooth connected solvable groups.

Let `g` carry the first Borel range to the second. Conjugating the first torus
by `g` puts its all-test range inside the target Borel. Both it and the target
torus therefore factor through the target Borel. Ambient maximality implies
maximality of these factorizations inside that Borel. The published solvable
maximal-torus conjugacy theorem supplies a rational point `p` of the target
Borel conjugating the two factorizations.

The composite rational conjugator is the image of `p` in the ambient group
multiplied by `g`. Naturality of inner automorphisms proves the required torus
range equality. Conjugation by a point of the target Borel preserves that
Borel's range, giving both equalities for the same point.

This lemma works over every field. It assumes the supplied Borel range
conjugacy and does not assert the finite-field descent step.
