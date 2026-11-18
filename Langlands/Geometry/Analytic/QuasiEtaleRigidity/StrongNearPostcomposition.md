# Postcomposition of the test relations

Author: Worker 931.

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It proves that
Berkovich's test relations (Library `IsNear`) are preserved by postcomposition
with a morphism, at the cost of finitely many test triples on the source,
provided that the preimage of the test domain is compact. This is internal.

## Charts

- `exists_chart_image_of_isQuasiIso`: let `t` be a quasi-isomorphism of
  saturated presentations. The image `t(Q)` of a chart `Q` is a chart `D` of the
  target, and `t.pullback Q D` represents the whole spectrum. The image is the
  local domain represented by `t.pullback Q m`; saturation makes it a chart.
- `exists_charts_nhds_preimage` and `exists_finite_charts_cover_preimage`:
  near each point of `c⁻¹(j)`, finitely many source charts mapped by `c` into
  the chart `j` cover a neighbourhood within `c⁻¹(j)`. They are built from the
  net property in the target and `StrongHom.exists_chart_inter_preimage`.
  Hence a compact `c⁻¹(j)` is covered by finitely many such charts.

## Strong form

`StrongNear.postcomp`: let `t` be injective on points. Let finitely many charts
`Q i` of `T`, each mapped by `c` into the domain of `τ'`, cover `c⁻¹` of that
domain. Let `D i` be the charts `t(Q i)`, and let functions `G i` on them pull
back along `t` to the pullbacks along `c` of the function of `τ'`. Then the test
relations for `(D i, G i, bound of τ')` between `α ≫ t` and `β ≫ t` give
`StrongNear τ' (α ≫ c) (β ≫ c)`. Injectivity of `t` turns membership in `D i`
for `α ≫ t` into membership in `Q i` for `α`. The bound is checked on a
subchart, as in `StrongNear.precomp`, using
`(α ≫ c)* f = α*(c* f) = α*(t* G) = (α ≫ t)* G`.

`exists_two_ore`: two strong maps lift simultaneously through a
quasi-isomorphism after one quasi-isomorphic refinement.

## Localized form

`exists_nearNumerators_postcomp` and `exists_isNear_postcomp`: let `f : V ⟶ U`,
and let `τ'` be a test triple on `U` with `f⁻¹(τ'.locus)` compact. There is a
finite set `E` of test triples on `V`, with domains inside `f⁻¹(τ'.locus)`, such
that `IsNear τ φ ψ` for all `τ ∈ E` implies `IsNear τ' (φ ≫ f) (ψ ≫ f)`.

Proof. Write `map t ≫ f = map c` with `t` a quasi-isomorphism. Then
`c⁻¹(τ'.locus) = t⁻¹(f⁻¹(τ'.locus))` is compact, because the base map of `t` is
a homeomorphism. Cover it by charts `Q`, and take `E` to be the triples on the
charts `t(Q)` whose functions are the inverse images, under the represented
isomorphisms (`Represents.univInverse`), of the pullbacks of the function of
`τ'`. Given `E`-near `φ, ψ`, merge the witnesses
(`exists_strongNear_numerators_aux`), lift through `t` (`exists_two_ore`), and
apply `StrongNear.postcomp`. No Lipschitz estimate is needed, because the test
functions are transported exactly.
