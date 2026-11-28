# Geometric reducedness, generic smoothness and generic freeness over a field

Over a field `k`:

- `isGeometricallyReduced_of_forall_eq_zero`: an algebra which embeds jointly into a family of
  geometrically reduced algebras is geometrically reduced.
- `isGeometricallyReduced_localization`: localizations preserve geometric reducedness.
- `linearIndepOn_pow_of_isGeometricallyReduced`: over a field `k` of characteristic `p`, taking
  elementwise `p`-th powers preserves `k`-linear independence of a finite family in a geometrically
  reduced field extension `K` (via `AlgebraicClosure`).
- `formallySmooth_of_isGeometricallyReduced`: a geometrically reduced field extension essentially of
  finite type is formally smooth (separably generated, via Mathlib's
  `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`).
- `exists_free_smooth`: for a non-zero geometrically reduced algebra of finite type `B` and a
  finite `B`-module `M`, there are a prime `q` of `B` and elements `r₁, r₂ ∉ q` such that
  `M[1/r₁]` is free over `B[1/r₁]` and `B[1/r₂]` is smooth over `k`. (A single basic open is
  obtained in `GoodChart.goodChartStatement` by taking the product `r₁ r₂`.)

These are the facts of Bosch–Lütkebohmert–Raynaud, *Néron Models*, §2.2, Proposition 16 and §3.3,
Lemma 4 (printed p. 67) used for good charts.
