# Simple transitivity of the Weyl action on Borels through a maximal torus

Workers 198 and 363.

This proof imports the unchanged published `WeylBorelSimplyTransitiveStatement`.
The theorem `Langlands.GroupScheme.weylBorelSimplyTransitive` proves that exact
proposition in every universe. It applies to every smooth connected affine
group over an algebraically closed field, with a prescribed maximal torus and
a Borel subgroup containing it.

The helpers in `Langlands.GroupScheme.WeylBorel` implement the three clauses.
For transitivity, Borel conjugacy first sends the chosen Borel to the target.
Maximal-torus conjugacy inside the target Borel corrects the conjugating point
by a point of that Borel. The product normalizes the prescribed torus and
still sends the first Borel to the target.

For centralizer invariance, a generic cocharacter of the split maximal torus
has the same all-test centralizer. The represented centralizer is a Cartan
subgroup, hence smooth, connected and nilpotent, and thus solvable. The
centralizer–Borel intersection theorem supplies a Borel of this Cartan subgroup
lying in the chosen ambient Borel. Maximality against the entire solvable
Cartan subgroup makes this inclusion an isomorphism. Consequently the entire
torus centralizer lies in the ambient Borel. Conjugation by any of its base
points therefore preserves that Borel.

For freeness, range invariance implies abstract point normalizer membership.
The Borel normalizer theorem places the point in the Borel. The helper in
`SolvableTorusNormalizer` applies to its smooth connected solvable group:
the prescribed torus maps monomorphically to a split torus quotient with
unipotent kernel. Inner conjugation acts trivially on that commutative
quotient, so cancellation forces the normalizing automorphism of the torus
to be the identity. Transport along the Borel inclusion gives the required
ambient centralizer membership. Worker 363 supplied the helper module and
its stronger closed-torus version; Worker 198 supplied the remaining proof
and the final assembly.

The source target is Milne, *Algebraic Groups* (2017), Corollary 17.11,
printed p.355, and Proposition 17.53, printed p.369 (registered source
`milne-2017-algebraic-groups`). The official errata snapshot registered as
`milne-2017-algebraic-groups-errata-2026-11-02` does not correct either result.
The transitivity argument follows the correction in 17.11. The centralizer
containment and quotient-cancellation arguments above are derived from the
imported published Library theorems; they replace the finite-fixed-locus and
commutator arguments in the printed proof of 17.53. No reductivity hypothesis
is used. Each helper is internal derived content supporting the exact target.
