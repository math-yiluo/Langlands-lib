# Presentation transport of actual curve-place restricted products

Author: Worker 208.

For fields `k`, `F` and `F'` in an arbitrary common universe, with
`k`-algebra structures on the latter two, `curvePlaceAdeleCongr e` is a
ring equivalence between their actual `CurvePlaceAdeleRing` objects for a
specified algebra equivalence `e : F ≃ₐ[k] F'`.
`curvePlaceAdeleHomeomorph e` has this same underlying equivalence and
preserves the existing restricted-product topologies.

The construction reuses the published equivalence `curvePlaceEquiv e`
of concrete curve places and the local comparison
`curvePlaceCompletionCongr e v`. The latter preserves membership in the
completed integer rings. Reindexing a cofinite family along an equivalence
preserves its cofinite property, so the dependent product equivalence
restricts to the actual restricted products. Coordinatewise preservation
of addition and multiplication supplies the ring equivalence.

`curvePlaceAdeleCongr_apply` identifies its coordinate at the transported
place with the local completion comparison of the original coordinate.
`curvePlaceAdeleCongr_symm_apply` gives the inverse coordinate using the
same local comparison's inverse. Mathlib's continuity theorem for maps
along an index map proves continuity in both directions; the forward
map includes the equality transport needed by its dependent local types.
These continuity proofs supply the homeomorphism without changing either
topology.

This is derived infrastructure for presentation independence of the
adelic level constructions motivated by Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
p.1 and pp.6–8, especially the completed local factors in Theorem 3.6.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The construction applies without a global-field hypothesis and does not
identify alternative conventions for global places. Finite poles, the
full-field diagonal, identity and composition laws, and geometric
point-space comparisons remain separate obligations.
