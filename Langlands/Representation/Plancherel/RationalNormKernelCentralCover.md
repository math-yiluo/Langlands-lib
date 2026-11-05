# Finite central Cartan covers on the rational norm kernel

This internal supporting unit supplies the compact envelope needed after a
uniform coefficient argument bounds the positive Cartan exponents. It proves
no existence of Cartan charts and no coefficient vanishing bound.

For a subgroup `K` and a set `T` in a topological group,
`centralDoubleCover K T` is the actual set `K T K Z(G)`, with multiplication in
the stated order and the full abstract center. A central coset meets a subgroup
`H` either in the empty set or in a translate of `H ∩ Z(G)`.
`isCompact_subgroup_central_coset` proves compactness of this intersection
from compactness of `H ∩ Z(G)`.

`isCompact_centralDoubleCover_preimage` assumes that `H` is closed, that `K`
is compact and contained in `H`, that `H ∩ Z(G)` is compact, and that `T` is
finite. Its conclusion is compactness of the literal preimage of `K T K Z(G)`
in `H`, equipped with its inherited subgroup topology. The proof takes the
finite union of the intersections `t Z(G) ∩ H`. Centrality moves the final
central factor past the second `K` factor, and containment `K ≤ H` identifies
the desired preimage with that of the compact product `K E K`. Closedness of
`H` makes its subtype inclusion a closed embedding, so this preimage is compact.
No quotient map or properness assertion is assumed.

The actual specialization uses the canonical topology on `G(F)` and the
existing `Plancherel.rationalCommonNormKernel G`. The published
`GroupScheme.rationalCenterComparison` identifies the full scheme center on
`F`-points with the abstract center. Together with the published
`BruhatTits.RationalPoints.centralNormKernelCompactness`, it proves
`isCompact_rationalCommonNormKernel_inf_center`. The existing norm-kernel
topology results give closedness and the inclusion of every compact subgroup
in the norm kernel. Consequently
`isCompact_rationalNormKernel_centralDoubleCover` needs only a connected
reductive group over a nonarchimedean local field, a compact subgroup `K`, and
a finite set `T`. It covers arbitrary characteristic, residue characteristic,
rank and splitness. It does not posit a Cartan decomposition.

The construction is derived from elementary group identities and compactness
of finite unions and products. Its role follows the compact central-intersection
step in Renard, *Représentations des groupes réductifs p-adiques* (2026),
VI.2.1(b) to (c), printed pp. 137–139 / PDF pp. 143–145. The compactness and
center-comparison theorems are reused by their published Lean names. The exact
uniform-support target and all its imported Lean/Markdown pairs are unchanged.
