# Normal compact-open bases and inherited intersections

This internal topology adapter addresses the basis and inherited-Levi topology clauses in the supplied-valid-data simultaneous-basis target. It uses the exact predicates of `SmallSubgroupPredicates`.

`CompactOpenNormalBasis.inherited` proves that the literal family `intersectionFamily M B` is a compact-open normal basis in every closed subgroup `M`. Normality is inherited by conjugation inside `K0 ∩ M`. Openness and the neighborhood basis pull back along the subgroup inclusion. Compactness pulls back along that closed embedding. There is no independent choice of a Levi basis.

`compactOpenNormalFamily K0` is the literal family of all compact open subgroups contained in `K0` and normal in it. `exists_compactOpenNormalBasis` uses Mathlib's `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` in the compact subgroup `K0`. The images of its open normal subgroups are compact and open in the ambient group because `K0` is compact and open. Their cofinality gives the full identity-neighborhood filter, as required by the published predicate.

This is an internal deduction from standard topological-group results, rather than a new source assertion. It proves none of the Iwahori, contraction or geometric Levi-restriction clauses, and does not identify a group-scheme topology with a subgroup topology.
