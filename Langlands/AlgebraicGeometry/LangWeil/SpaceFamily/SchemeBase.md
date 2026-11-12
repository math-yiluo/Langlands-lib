# The uniform Lang–Weil estimate for a separated algebraic space over a scheme

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal. This is the scheme-base case of the argument. The stratification follows the
strategy recorded in the statement's Markdown: the space is stratified by schemes, the top
stratum is counted by the Lang–Weil estimate in families, and the lower strata by the upper
bound. Here the strata come from the symmetric tuple charts `V_n` of a separated algebraic
space.

## Setting

`c` is a `SepChart`: a separated algebraic space `X`, an affine étale surjective chart
`a : U → X`, the symmetric tuple quotients `V_n` with étale maps `e_n : V_n → X`, and the
tuple-length bound `N`. `M` is a quasi-compact scheme locally of finite type over `ℤ`.
`g : X → h_M` is a morphism, and `π : U → M` is surjective and smooth of relative dimension
`d` with `a ≫ g = h(π)`. The maps `p_n : V_n → M` are those with `e_n ≫ g = h(p_n)`.

## Contents

- Elementary facts. `isLocallyNoetherian_of_locallyOfFiniteType`: a scheme locally of finite
  type over `ℤ` is locally Noetherian. `eq_bot_of_lt_zero` and `le_coe_pred_of_lt` are
  inequalities in `WithBot ℕ∞`. `isEmpty_of_topologicalKrullDim_lt_zero`: a space of
  dimension below `0` is empty.
- `isOpen_range_p`: the image of `p_n` is the image under `π` of the image of the étale first
  coordinate `W_n → U` (`symmetricMap_p`, with `W_n → V_n` surjective), hence open, since
  smooth and étale maps are open.
- `exists_mem_range_p` and `exists_inStratum`: since `π` is surjective, every point `y` of
  `M` is `π x`. An `Ω`-point through `x` (with `Ω` an algebraic closure of the residue field)
  is the image of an `Ω`-point of some `V_n` with `n < N` (`exists_ptE_eq`), so `y` lies in the
  image of `p_n`. The largest such `n` gives the stratum of `y`.
- `stratumClosed k` is the closed set of points in no image of `p_n` for `k < n < N`.
  `stratum k` is the open subscheme over the image of `p_k` of the reduced closed subscheme on
  `stratumClosed k` (`Scheme.IdealSheafData.vanishingIdeal`). Its immersion into `M` is
  `stratumι k`, a preimmersion locally of finite type. Its points are exactly in the stratum
  of degree `k` (`inStratum_stratumι`). A field point of `M` in that stratum factors through
  it (`exists_lift_stratumι`): the point lifts to the reduced closed subscheme because
  `Spec κ` is reduced, then to the open subscheme. The stratum is quasi-compact
  (`compactSpace_stratum`, since `M` is Noetherian) and locally of finite type over `ℤ`
  (`locallyOfFiniteType_stratum`).
- `stratumFamilyEquiv`: the `κ`-points of `V_k ×_M stratum k` over a lift `m'` of `m` are
  the `κ`-points of `V_k` over `m`.
- `geometricallyIrreducible_stratumFamily`: if the points of every fibre of `g` over a field
  point are irreducible, then `V_k ×_M stratum k → stratum k` has geometrically irreducible
  fibres. Each such fibre is the fibre of `p_k` over a field point in the stratum of degree
  `k`, by pasting pullbacks, and these are irreducible by `irreducibleSpace_pullback_p`.
- `exists_bound_top`: `FamilyLangWeilStatement` applied to `V_k ×_M stratum k → stratum k`
  (pure fibre dimension `d` by base change of `pureFibreDimension_p`) gives `C > 0` with
  `|#{v ∈ V_k(κ) | v ↦ m} − (#κ)^d| ≤ C (#κ)^(d − 1/2)` for every `m` in the stratum of
  degree `k`.
- `exists_bound_lower`: `FamilyPointUpperBoundStatement` applied to `D_n → V_n → M` gives
  `C > 0` with `#{x ∈ D_n(κ) | x ↦ m} ≤ C (#κ)^(d − 1/2)` for `m` in a stratum of degree
  `k > n`. The fibre of `D_n` over `m` has dimension below `d` (`topologicalKrullDim_fiber_lt`).
  For `d ≥ 1` the upper bound with `e = d − 1` gives `C (#κ)^(d − 1) ≤ C (#κ)^(d − 1/2)`.
  For `d = 0` the fibre is empty, and so is the set of points.
- `uniformLangWeil_schemeBase`: under the hypotheses above, and if the points of the fibre of
  `g` over every field point of `M` form a connected space, there is `C > 0` with
  `|#{z ∈ X(κ) | z ↦ m} − (#κ)^d| ≤ C (#κ)^(d − 1/2)` for every finite field `κ` and every
  `m : Spec κ → M`. The fibre points are irreducible (`irreducibleSpace_points_fib`). Let `k`
  be the stratum of `m`. By `card_fibrePoints` the count is `∑_{n < N} #D_n(κ)_m`. The terms
  with `n > k` vanish, since `m` is in no image of `p_n`. The term `n = k` is
  `#{v ∈ V_k(κ) | v ↦ m}`, since these points lie outside the threshold
  (`not_mem_threshold_of_inStratum`). The terms `n < k` are bounded by `exists_bound_lower`.
  The constant is `1 + ∑_k C_k + ∑_n C'_n`.
