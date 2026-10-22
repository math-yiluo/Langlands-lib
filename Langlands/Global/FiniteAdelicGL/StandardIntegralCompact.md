# Compactness of the standard integral finite adelic subgroup

This module proves `standardIntegralCompact` with the exact published target
`StandardIntegralCompactStatement`: for every number field `K : Type u` and
every natural rank `n`, the carrier of `standardIntegral K n` is compact.
The field assumptions are exactly `[Field K] [NumberField K]`. The subgroup
is already bundled as an `OpenSubgroup` in `StandardIntegralStatement`.

The construction and proof have internal, derived provenance. They combine the
integral finite-adele compactness theorem and the generic integral matrix
subgroup theorem with elementary subring extensionality and product topology.
No external theorem is quoted and no completion or reciprocity object is
introduced.

`integralAdeles_eq_integralFiniteAdeles` identifies the shared
`integralAdeles K` with its alias `Langlands.Global.integralFiniteAdeles K` as
subrings of the actual finite adele ring. Both names are housed in the imported
`IntegralFiniteAdeles` module. Subring extensionality reduces equality to
membership of an arbitrary finite adele. Both predicates are definitionally
the condition that every finite-place coordinate belongs to that place's
`adicCompletionIntegers K`. Reflexivity proves the equivalence.

The compactness proofs directly reuse
`Langlands.Global.isCompact_integralFiniteAdeles`, since the two subrings are
definitionally equal. The imported compactness theorem uses the published
`CompletionPadic` local-field certificate and valuation-order comparison to
identify each completed integer ring with a compact closed valuation ball.
The continuous restricted-product structure map sends the compact product of
these local integer rings onto the integral finite-adele subring. Thus the
imported theorem uses the existing restricted-product topology on actual finite
adeles. Its paired Markdown describes that proof in detail.

`isCompact_integralMatrices` rewrites the carrier using the published
`integralMatrices_eq_pi` and applies `isCompact_univ_pi` twice. The matrix locus
is therefore compact in its finite product topology.

`isCompact_standardIntegral` obtains Hausdorffness from the restricted product
of the actual Hausdorff completions, then applies the published
`Langlands.GeneralLinearGroup.isCompact_integralSubgroup` to `Fin n` and
`integralAdeles K`. The finite-adele ring's existing topological-ring structure
supplies continuity of the ring operations. The generic theorem uses
`IsCompact.matrix` and `Submonoid.units_isCompact`: the units topology is induced
by the value/inverse pair, whose image is closed by the equations `AB = 1` and
`BA = 1`. Both matrices range over compact integral matrix sets, so the
inverse-pair locus is compact. The bundled subgroup has exactly this carrier.

Both the forward matrix and its inverse must have integral entries. A matrix
can have integral entries and be invertible over the ambient coefficient ring
while its inverse has nonintegral entries. The `Submonoid.units` construction
imposes both requirements, as expressed by the published coordinate theorem
`mem_standardIntegral`. No topology is replaced.

All finite products and the generic subgroup argument permit `Fin 0`; no
positive-rank hypothesis occurs. The published `standardIntegral_zero` states
that the rank-zero open subgroup is the top subgroup. Finally,
`standardIntegralCompact` introduces the number field, its two instances, and
the natural rank, then applies `isCompact_standardIntegral`.

The reusable new names are `integralAdeles_eq_integralFiniteAdeles`,
`isCompact_integralMatrices`, `isCompact_standardIntegral`, and
`standardIntegralCompact`, all in
`Langlands.Global.FiniteAdelicGL`. Worker 190 supplies the subring compatibility
lemma; Worker 74 assembles the compactness proof.
