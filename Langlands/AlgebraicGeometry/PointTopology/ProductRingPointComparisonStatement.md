# Product-ring point comparison: exact statement

`ProductRingPointComparisonStatement` states Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (31 December 2011), formula (3.6.2) and its injectivity
and surjectivity assertions on printed pages 7–8. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The affine clause also records the affine case proved at the end of the
surjectivity argument on page 8.

For every commutative base ring `C`, every family of commutative `C`-algebras
`R i`, and every scheme `X` over `Spec C`, the actual relative map

`productPointMap C R X : X(∀ i, R i) → ∀ i, X(R i)`

has the following independently quantified properties:

- If `X.left` is quasi-separated, the map is injective. There is no
  quasi-compactness or local-factor hypothesis in this clause.
- If `X.left` is affine, the map is surjective for arbitrary factors.
- If `X.left` is quasi-compact and every `R i` is a local ring, the map is
  surjective. There is no quasi-separatedness or separatedness hypothesis in
  this clause.

`QuasiSeparatedSpace X.left` is the intrinsic scheme quasi-separatedness
condition in the source, stated there as quasi-compact overlap of quasi-compact
opens. `CompactSpace X.left` expresses quasi-compactness; it imposes no
Hausdorff condition. Neither the scheme nor its structure morphism is assumed
finite type. The index set may be infinite or empty. All rings and the index
set lie in an arbitrary common universe, as in the published map and the
pinned Mathlib interfaces.

The statement uses the actual slice-category points and product algebra from
`ProductRingPoints`. It does not assume any comparison theorem as structure
data. Combining the first and third clauses gives bijectivity for a
quasi-compact quasi-separated scheme with local factors, which is the
set-theoretic product-ring input to (3.6.1). Adelic realization, finite-type
models, and the topology in (3.6.1) remain separate obligations.
