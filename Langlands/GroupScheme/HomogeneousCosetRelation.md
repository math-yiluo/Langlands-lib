# The actual right-coset relation

Author: Worker 148.

This internal construction is the relation used for the general homogeneous quotient target. For an actual homomorphism `i : H → G` of group schemes over any base scheme `S`, the arrow scheme is `G ×_S H`, and its two projections are `(g,h) ↦ g` and `(g,h) ↦ g i(h)`. All point statements quantify over every scheme over `S`, including nonaffine and nonreduced schemes.

The right difference morphism on `G ×_S G` is `(g,h) ↦ g⁻¹h`. The inclusion of the arrow scheme is its pullback of `i`; the proof constructs the universal lift by retaining the first group coordinate and the subgroup coordinate. A closed subgroup therefore gives a closed immersion of the relation. The target projection is the source projection composed with the actual automorphism `(g,h) ↦ (g i(h),h)`. Both projections are smooth when `H` is smooth over `S`.

The all-test arrow-existence criterion is precisely membership of `g⁻¹h` in the already published `SubgroupFunctor.range i`. Consequently, any actual scheme morphism with this relation as kernel pair has exactly the required all-test coset fibers. This construction does not claim existence of a quotient scheme.

The provenance is the intrinsic group-object construction behind Milne, *Algebraic Groups* (2017), Definition 5.20 and Proposition 5.24, printed pp.104–105. Unlike the source's initial algebra-test description, the implemented group-object proof works directly in the full scheme slice. The original source is registered as `milne-2017-algebraic-groups`; its full registered author errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` changes neither passage.
