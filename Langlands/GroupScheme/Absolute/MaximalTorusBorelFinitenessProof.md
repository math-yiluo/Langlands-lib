# Finitely many Borel subgroups through a maximal torus

This module proves the unchanged published proposition
`Langlands.GroupScheme.MaximalTorusBorelFinitenessStatement.{u}` as
`Langlands.GroupScheme.maximalTorusBorelFiniteness`, in every universe `u`.
Its field is algebraically closed, and its ambient group is smooth, affine
and connected. No reductivity assumption is used.

The source target is James S. Milne, *Algebraic Groups* (2017), registered
source `milne-2017-algebraic-groups`, Corollary 17.26(a), printed p.360.
The normalizer-transitivity argument is Corollary 17.11, printed p.355.
The proof below also uses the published formalizations of Cartan structure
(Proposition 17.44, printed pp.364–365) and the centralizer Borel intersection
theorem (Theorem 17.46, printed pp.365–366). The original PDF passages on
pp.355, 360 and 365 were read for this implementation. The registered official
2017 errata snapshot of 2 November 2026 was checked; its p.360 correction
concerns the dimension example preceding Proposition 17.28, and does not
change this corollary.

## Implemented proof

The proof imports the statement and its existing dependencies without editing
them. Every containment of subgroup functors holds on every test scheme.

1. `MaximalTorusBorelFiniteness.centralizer_le_borel` chooses a closed
   representative `C` of the whole maximal-torus centralizer. The published
   `cartanStructure` makes `C` smooth, connected and geometrically nilpotent,
   hence solvable. A torus over the algebraically closed field is split, and
   the published generic-cocharacter theorem supplies a cocharacter with the
   same centralizer. The published `centralizerBorelIntersection` places a
   Borel subgroup of `C` inside the prescribed ambient Borel. Since `C`
   itself is smooth, connected and solvable, Borel maximality makes this
   subgroup equal to `C`.
2. `MaximalTorusBorelFiniteness.exists_normalizer_conjugating_borel` first
   conjugates one Borel to the other. The two resulting embeddings of the
   maximal torus in the second Borel are maximal there and can be conjugated
   inside that Borel. Correcting the original conjugating point by this
   Borel point gives a normalizer point with the desired conjugate range.
3. `MaximalTorusBorelFiniteness.range_conjugate_mul` records that right
   multiplication of a conjugating point by a point of the subgroup leaves
   its conjugate range unchanged. It follows directly from naturality of
   inner automorphisms and invariance of a range under a source isomorphism.
4. The final theorem uses published finiteness of the full character-lattice
   Weyl image of a closed split torus. The kernel of this action is exactly
   its centralizer, so the actual quotient `N(k)/C(k)` is finite. Centralizer
   containment from step 1 makes the conjugate-range map descend to this
   quotient. Step 2 puts every Borel subgroup functor in the statement into
   the image of that map, and a subset of a finite image is finite.

These helper lemmas are internal derivations from the cited published
results. The proof uses the full centralizer and the finite Weyl quotient;
Milne's proof of Corollary 17.26(a) instead bounds the number by the
components of the normalizer. Both yield exactly the set finiteness required
by the published statement, which counts ranges rather than presentations.
