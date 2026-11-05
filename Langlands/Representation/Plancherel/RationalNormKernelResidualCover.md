# Restricting central residual covers to the rational norm kernel

This internal supporting construction restricts a supplied central Cartan cover
to a subgroup with compact central intersection. It does not construct Cartan
parameters, corrected cocharacters, small levels, or a coefficient bound.

`centralResidualNormalizer H Γ` is the subgroup of `H` obtained by taking
the preimage of `Γ ∨ (H ∩ Z(G))` under the subtype inclusion `H → G`.
The definition needs only a group. Its compactness and normalization
properties in the cover theorem below use the stated topological and
normalization hypotheses.

For any group `G`, subgroup `H`, and finite set `T`,
`exists_finite_subgroup_central_representatives` chooses one representative in
`H` for each coset `f Z(G)` with `f ∈ T` that meets `H`. Its finite set `R`
lies in the actual subtype `H`. For every central `z` with `f z ∈ H`, it gives
`f z = r c`, where `r ∈ R` and `c ∈ H ∩ Z(G)`. The construction selects one
central correction for each relevant member of `T`. The difference of any
other correction and the selected one lies in `H ∩ Z(G)`.

`isCompact_sup_of_central` proves that adjoining a compact central subgroup
to a compact subgroup preserves compactness. The central subgroup is normal,
so the underlying set of the join is their pointwise product.

In a topological group, assume `H` is closed, `Γ` is compact and contained in
`H`, `Γ` normalizes a supplied subgroup `K`, and `H ∩ Z(G)` is compact.
For an arbitrary index type `A`, let `e : A → H` be subgroup-valued parameters.
Assume every `g ∈ H` has an ambient expression
`g = γ (e(a) f) γ' z`, with `γ, γ' ∈ Γ`, `f ∈ T`, and `z ∈ Z(G)`.
The theorem `exists_compact_subgroup_residual_cover_of_central_cover`
produces a compact subgroup `ΓH` of `H` containing the preimage of `Γ`,
normalizing the preimage of `K`, and a finite `R ⊆ H` such that every `g ∈ H`
has the literal expression `g = γH (e(a) r) γH'`.

The proof uses `centralResidualNormalizer H Γ`. Compactness follows from the compact product and closed
embedding. Both original compact factors still normalize `K`. Centrality
moves `z` past the last `Γ` factor. Cancellation shows `f z ∈ H`; the finite
representative lemma then replaces this term by `r c` and absorbs `c` into
the last compact factor. No commutation or normalization of the residual
representatives is needed. The index type need not be finite or nonempty.

`Plancherel.exists_rationalNormKernel_residual_cover` specializes to the actual
`Plancherel.rationalCommonNormKernel G` of any connected reductive group over a
nonarchimedean local field. It uses the canonical rational-point topology and
the inherited subgroup topology. Closedness of the kernel, containment of
compact subgroups, and compactness of its intersection with the full abstract
center are reused from the published norm-kernel topology, rational-center
comparison, and central norm-kernel compactness results. The ambient compact
normalizer and the central Cartan cover remain supplied hypotheses.

The construction is derived from elementary group identities and compactness
of products and closed-embedding preimages. It provides the restriction step
needed to apply a finite-residual Hecke sandwich to the norm kernel in the
uniform-support route through Renard, *Représentations des groupes réductifs
p-adiques* (2026), V.5.3 and VI.2.3–VI.2.4. This is an internal adapter; no
claim is made that the source supplies its exact formulation. The exact
uniform-support proposition and its imported pairs remain unchanged.
