# Scheme-theoretic intersections of closed subgroups

Author: Worker 308.

This is internal categorical infrastructure for the intersection of
rational parabolic subgroups in Borel–Tits, *Groupes réductifs* (1965),
Proposition 4.7. The constructions and proofs follow the universal
property of a pullback, and do not assert the geometric structural
claims of that proposition.

For two group scheme homomorphisms `j : P ⟶ G` and `j' : P' ⟶ G`
over any base scheme `S`, `subgroupIntersection j j'` is their actual
pullback in group schemes. It comes with the two projection
homomorphisms and the common composite `subgroupIntersectionHom j j'`
into `G`. The pullback square remains a pullback after forgetting the
group structure and after forgetting the structure maps to `S`.

The range of the common composite is the intersection of the two ranges
on every test scheme. The proof lifts any two points with the same
ambient image through the pullback; the converse uses its two
projections. If both original maps are closed immersions, base-change
stability and composition of closed immersions make the common
composite a closed immersion as well. It therefore represents the
intersection subgroup functor in the published sense.

The module also constructs the canonical isomorphism between arbitrary
base change of this intersection and the intersection after base change,
and proves compatibility with the common composite into the ambient
group.

These results require no field or reductivity assumptions. They prove
representability and closedness, with arbitrary base change. Smoothness,
connectedness, maximal rank, and existence of a rational maximal torus
in an intersection of parabolics remain separate geometric obligations.
