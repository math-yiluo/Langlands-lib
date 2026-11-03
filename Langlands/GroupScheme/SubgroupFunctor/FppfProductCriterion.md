# A geometric criterion for represented fppf products

This internal adapter proves
`Langlands.GroupScheme.SubgroupFunctor.isFppfProduct_of_fppf_factorization`
over any base scheme. Given two group homomorphisms `i : H ⟶ G` and
`j : N ⟶ G`, a closed subgroup `p : P ⟶ G`, and a flat, surjective,
locally finitely presented map `q : H.X × N.X ⟶ P.X` whose composite with
`p` is ordered multiplication, `p` satisfies the existing all-test
`IsFppfProduct (range i) (range j)` predicate.

For a point of `P` on an arbitrary relative test scheme, the proof pulls back
`q`. The pullback is a single fppf cover and its two coordinates supply the
required ordered factorization. Conversely, a local factorization by points
of `H` and `N` factors through `q` on the cover. The published effective
epimorphism descent lemma `mem_range_of_comp_mem_range` descends this
factorization through the closed, hence monic, map `p`.

This is a formal consequence of the published product and represented-image
descent interfaces, not an existence theorem for `P` or `q`. It is the
all-test adapter for the semidirect-image construction described by Milne,
*Algebraic Groups* (2017), Theorem 5.82, printed pp. 120–121 (registered
source `milne-2017-algebraic-groups`).
