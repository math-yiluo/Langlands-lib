# Reduction of étale pair descent to descent along one étale cover

This module proves

`Langlands.GroupScheme.affineWeilPairEtaleDescent_of_singleChart
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hS : AffineWeilPairSingleChartDescentStatement.{u}) :
  AffineWeilPairEtaleDescentStatement.{u}`.

Étale-locally given Weil-restriction presentations, on an arbitrary covering family of étale
charts, therefore descend once two inputs are proved: factor rigidity
(`WeilFactorIdempotentRigidityStatement`) and descent along a single étale cover
(`AffineWeilPairSingleChartDescentStatement`). The theorem takes both as hypotheses and adds no
other assumption.

## Auxiliary results

- `isAlmostSimple_geometricFiber_baseChange_of_etale`: for an étale morphism `b : T → S` and a
  group scheme `G` over `S` whose geometric fibres are almost simple, every geometric fibre of
  the base change `G_T` is almost simple. The residue field extension `κ(b t) ⊆ κ(t)` is
  separable algebraic, since `b` is étale. The chosen algebraic closure of `κ(t)` is therefore
  algebraic over that of `κ(b t)`.
  `RelativeLevi.geometricFiberBaseChangeIso` identifies the geometric fibre of `G_T` at `t`
  with the base change of the geometric fibre of `G` at `b t` along this extension. The
  geometric fibre of `G` is absolutely almost simple by `separablyClosedAlmostSimpleAbsolute`,
  and absolute almost-simplicity persists along algebraic extensions
  (`IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`).
- `exists_finset_etale_cover`: the images of the spectra of a covering family of étale
  `A`-algebras are open (étale morphisms are open maps). Since `Spec A` is quasi-compact,
  finitely many charts already cover.
- `etale_tensor_right`: for an étale `A`-algebra `R` and any `A`-algebra `B`, `R ⊗[A] B` is
  étale over `B` through its right factor.
- `factor_reductive_almostSimple`: the base change of a reductive group with almost simple
  geometric fibres along `Spec (R ⊗[A] B) → Spec B`, for étale `R`, has the same properties.
- `exists_chart_comparison`: suppose `G ≅ R_{B/A}(G')` and, over an étale `A`-algebra `R`,
  `G_R ≅ R_{B'/R}(G₁)`, with both pairs reductive with almost simple geometric fibres. Base
  change of Weil restriction (`AffineWeil.BaseChange.iso`) gives an isomorphism
  `R_{(R ⊗ B)/R}(G'_{R ⊗ B}) ≅ R_{B'/R}(G₁)`.
  `WeilFactor.exists_baseChange_iso_of_weilRestriction_iso` (in `WeilFactorUniquenessReduction`) then gives an `R`-algebra
  isomorphism `α : B' ≃ R ⊗[A] B` and an isomorphism `(G₁)_α ≅ G'_{R ⊗ B}`. The comparison
  required by the target statement uses `e := α.symm`. The base change of `G'` along the
  spectrum of `b ↦ e (1 ⊗ b)` is rewritten with the base-change composition and identity
  isomorphisms (`baseChangeCompIso`, `baseChangeIdIso`) until it becomes `G₁`.
- `surjective_of_charts`: if each `Spec (B' i) → Spec (R i)` is surjective, the charts cover
  `Spec A`, and `R i ⊗[A] B ≃ B' i` as `R i`-algebras, then `Spec B → Spec A` is surjective.
  A point of `Spec (B' i)` over a point of `Spec (R i)` maps to a point of `Spec B` over the
  same point of `Spec A`, because the two composite ring maps `A → B'_i` agree.

## Proof of the main theorem

Choose finitely many charts that still cover (`exists_finset_etale_cover`). Combine them with
`AffineWeil.ChartCombination.combinedIso` into one presentation over the product chart
`A' = ∏ R i`, with coefficient algebra `C = ∏ B' i` and the assembled group `H`. The product is
étale over `A` (Mathlib's instance for finite products), and its spectrum maps onto `Spec A`
(`surjective_baseMap`). `C` is finite, projective and étale over `A'`, and `H` is reductive with
almost simple geometric fibres (`isReductive`, `isAlmostSimple_geometricFiber`). The hypothesis
`hS` gives `B` and `G'` with `G ≅ R_{B/A}(G')`. For every chart of the original family, selected
or not, `exists_chart_comparison` gives the required comparison `R i ⊗[A] B ≃ B' i` and
`G'_{B' i} ≅ G₁ i`. These comparisons give surjectivity of `Spec B → Spec A` by
`surjective_of_charts`.

## Provenance

This is an internal reduction. It follows the outline of Conrad, *Reductive group schemes* (2014),
proof of Proposition 6.4.4: étale descent combined with uniqueness of the pair. Conrad's
uniqueness assertion appears here through factor rigidity. It is used only to recover the local
pairs from the descended one.
