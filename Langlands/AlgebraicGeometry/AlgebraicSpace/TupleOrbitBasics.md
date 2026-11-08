# Basic facts for tuples of points of a finite cover

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitBasics`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Throughout, `f : h_U ⟶ X` is a map from the
presheaf represented by a scheme `U` over `S` to a presheaf `X` on `Over S`.

## Relative finiteness and surjectivity

- Four instances: the properties "the underlying scheme morphism is finite" and "the
  underlying scheme morphism is surjective" on morphisms of `Over S`, that is,
  `MorphismProperty.inverseImage` along `Over.forget S`, are stable under base change and
  under composition. Base change uses `MorphismProperty.of_isPullback` on the image of the
  pullback square under `Over.forget S`. Composition uses `Over.comp_left`.
- `IsFinite.map_comp φ hφ hf`: if `φ : U' ⟶ U` has finite underlying morphism and `f` is
  finite (relative to `schemeYoneda S`), then `h_φ ≫ f` is finite. `MorphismProperty.relative_map`
  makes `h_φ` relatively finite, and the relative property is stable under composition.
- `IsSurjective.map_comp`: the same statement for surjectivity.

## Fibre powers

For the published `ChartFibrePower`:

- `ChartFibrePower.sameImage_pr P p i j`: two coordinates of a point `p` of a fibre power have
  the same image (published `SameImage`), witnessed by the fibre power itself.
- `ChartFibrePower.fin_pr_last_isFinite hf ha n`: if `f` is finite, the last projection of
  the standard fibre power `fin ha n` is finite. The proof is by induction on `n`. The last
  projection of `fin ha (n + 1)` is the base-changed projection `succSnd`, finite by
  `IsFinite.projection`, followed by the last projection of `fin ha n`.

## Bounded length of distinct tuples

`exists_bound_isDistinct hf γ`. For `f` finite and a point `γ` of `U`, there is `N` with the
following property. Whenever a fibre power `Q` indexed by `Fin m` has a point `q` with
pairwise distinct coordinates (`IsDistinct`) and some coordinate projection sends `q` to
`γ`, then `m ≤ N`.

Proof. Let `R = fin ha 1` be the twofold fibre power. Its last projection is finite, so
`exists_card_le_of_isFinite` applied to it and `γ` gives a bound `N`. It bounds the number of
distinct `K`-points of `R` over a fixed `K`-point of `U` above `γ`, uniformly in the field
`K`. Let `K = κ(q)`. The `k`-th coordinate of `q` is a `K`-point of `U` above `γ`; write it
as `Spec α` followed by `fromSpecResidueField γ` (`Scheme.SpecToEquivOfField`). For each
index `j`, the pair (`j`-th coordinate, `k`-th coordinate) lifts to a `K`-point `r j` of `R`
by `ChartFibrePower.lift`. All `r j` lie over the same `K`-point of `U`. They are pairwise
distinct because their first projections are the distinct coordinates of `q`. Hence
`m ≤ N`.

## Provenance

Internal helpers for the tuple-orbit construction of task 13a3a0fd (see
`TupleOrbitCover`). No source proof is transcribed.
