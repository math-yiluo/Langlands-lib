# The uniform Lang–Weil estimate over a scheme chart of the base

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal.

Let `f : Y → B` satisfy the hypotheses of `SpaceUniformLangWeilStatement` apart from the
conditions on `B`. That is, `f` is separated, quasi-compact and surjective, with geometrically
connected fibres, and there is an étale chart square `a : U → Y`, `b : V → B`, `φ : U → V`
with `a` surjective and `φ` smooth of relative dimension `d`. Let `M` be an affine scheme
locally of finite type over `ℤ`, and let `t : h_M → B` be any morphism. The module reduces
the count of points of `Y` over `t ∘ m`, for `κ`-points `m` of `M`, to
`uniformLangWeil_schemeBase` applied to the fibre product `X = Y ×_B M`. `X` is the Library's
`ChartFibre.space f t`, a separated algebraic space because `f` is separated and
quasi-compact (`ChartFibre.isSeparated_space`). Its projection is
`g = ChartFibre.snd : X → h_M`.

## Contents

- `surjective_of_exists_point`: let `aO : h_O → F` be an étale surjective chart of a presheaf
  with `aO ≫ g = h(π)`. Suppose every point `y` of `M` is the image of a point `τ` of some
  scheme `T` with a morphism `z : h_T → F` over `M` (`z ≫ g = h(s)`, `s τ = y`). Then `π` is
  surjective. The point of `F` given by `z` at `τ` comes from a point `o` of `O`
  (`surjective_chartPointMap`). A common scheme `T'` with a point `τ'` mapping to `o` and to
  `τ` (`chartPointMap_eq_iff_sameImage₂`) shows `π o = s τ = y`.
- `exists_affine_chart`: an étale surjective chart `aP : h_P → F` with `aP ≫ g = h(π)` and `π`
  smooth of relative dimension `d` can be replaced by an affine one with the same
  properties, if `F` has a quasi-compact étale surjective chart `Q`. The pullback
  `W = P ×_F Q` is étale over `P` and étale surjective over `Q`. Finitely many affine opens of
  `W` cover `Q`, by quasi-compactness and openness of étale maps. Their disjoint union `O` is
  affine and étale over `W` (`IsZariskiLocalAtSource.sigmaDesc`). The composite `O → W → Q` is
  surjective, so `O → F` is étale surjective. `O → W → P → M` is smooth of relative dimension
  `0 + d`.
- `exists_smooth_chart`: `X` has the étale surjective chart `P = U ×_V (V ×_B M)`, smooth of
  relative dimension `d` over `M`. `V ×_B M` is the scheme representing the pullback of the
  étale map `b` along `t`, and is étale over `M`. The chart `P → X` is the base change of
  `a : U → Y` along the projection `X → Y` (pasting of pullback squares), hence étale
  surjective. `P → V ×_B M` is the base change of `φ`, hence smooth of relative dimension
  `d`, and so is its composite with the étale map `V ×_B M → M`.
- `connectedSpace_fib`: for a field point `s : Spec K → M`, the fibre of `g` over `s` is the
  fibre of `f` over the field point `t ∘ s` of `B`, by pasting pullbacks. Its points form a
  connected space because `f` has geometrically connected fibres
  (`Points.isoHomeomorph`).
- `fibreEquiv`: the `κ`-points of `X` over `m` are the `κ`-points of `Y` over `t ∘ m`, by the
  universal property of the fibre product.
- `uniformLangWeil_fibreProduct`: assuming `FamilyLangWeilStatement` and
  `FamilyPointUpperBoundStatement`, there is `C > 0` such that for every finite field `κ` and
  every `m : Spec κ → M`, the number `N` of `κ`-points `y` of `Y` with `y ≫ f = h(m) ≫ t`
  satisfies `|N − (#κ)^d| ≤ C (#κ)^(d − 1/2)`. Take the affine chart `O → X` from the two
  lemmas above, with the quasi-compact chart from `ChartFibre.exists_atlas_fibre`, and its
  kernel pair (`exists_kernelPair`). Together they form a `SepChart`. The map `O → M` is
  surjective by `surjective_of_exists_point`: a point `y` of `M` gives a point of `B`, which
  comes from a point of `Y` since `f` is surjective, and hence from a point of `U`. A common
  scheme over both gives a morphism to `X` hitting `y`. With `connectedSpace_fib`,
  `uniformLangWeil_schemeBase` applies, and `fibreEquiv` translates the count.
