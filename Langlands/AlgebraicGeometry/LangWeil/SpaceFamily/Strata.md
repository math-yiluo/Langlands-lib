# Degree strata of the base of a separated algebraic space with a smooth chart

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal.

Let `c` be a `SepChart` (a separated algebraic space `X`, an affine étale surjective chart
`a : U → X`, the symmetric tuple quotients `V_n`, the étale maps `e_n : V_n → X`), let
`g : X → h_M` be a morphism to a scheme, and let `p_n : V_n → M` be the scheme maps with
`e_n ≫ g = h(p_n)` (`Counting.lean`). `N` is the tuple-length bound.

## Contents

- `topologicalKrullDim_lt_of_isClosedEmbedding` (topology): let `j : G → F` be a closed
  embedding into a Noetherian space of dimension at most `d` whose image contains no nonempty
  open set. Then `dim G < d`. A chain of irreducible closed subsets of `G` maps to a chain in
  `F`. Its last member lies in an irreducible component `Y` of `F`. `Y` is not contained in
  the image of `j`, since it contains a nonempty open subset of `F`
  (`NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`). Appending `Y`
  lengthens the chain, so its length plus one is at most `d`.
- `e_g`: `e_n ≫ g = h(p_n)`.
- `mem_range_p_of_mem_threshold`: suppose a point `v` of `V_n` lies in the threshold open
  `tupleSymmetricThresholdOpen n (n + 1)`. Then `n + 1 < N` (the threshold of length `N + 1`
  is empty, `tupleThresholdOpen_eq_bot`), and `p_n v` is in the image of `p_{n+1}`. The
  first coordinate of a tuple over `v`, taken as a point with values in an algebraically
  closed field, starts a distinct tuple of length `n + 2` (`exists_tuple_of_mem_threshold`).
  The class of that tuple in `V_{n+1}` has the same image in `X`, hence in `M`.
- `InStratum k y`: `y` is in the image of `p_k` and in no image of `p_n` for `k < n < N`.
  `not_mem_threshold_of_inStratum`: the points of `V_k` over such a `y` lie outside the
  threshold open.
- `ptE_eq_of_fibChart` and `snd_eq_of_fibChart` compare points of the fibre charts
  `V_n ×_M T` and `V_k ×_M T` (`FibreCharts.lean`) with the same image in the fibre of `g` over
  `s : T → M`. They have the same image in `X` under `e_n` and `e_k`, and the same image in `T`.
- `irreducibleSpace_pullback_p` (irreducible fibres on the top stratum): let `s : Spec K → M`
  be a field point whose point lies in the stratum of degree `k`, and suppose the points of
  the fibre of `g` over `s` form an irreducible space. Then the scheme `V_k ×_M Spec K` is
  irreducible. It is nonempty because `s` lies in the image of `p_k`. Two nonempty open
  subsets of it contain `Ω`-points `ξ₁, ξ₂` with the same image in the fibre of `g`
  (`exists_common_point_of_isOpen`). Their first projections to `V_k` lie outside the
  threshold and have the same image in `X`, so they are equal (`eq_of_ptE_eq`). Their second
  projections agree by `snd_eq_of_fibChart`. Hence `ξ₁ = ξ₂`, and the two open subsets meet.
- `topologicalKrullDim_fiber_lt` (small fibres on the lower strata): let `y` lie in the
  stratum of degree `k`, with irreducible fibre points of `g` over `Spec κ(y)`, and let
  `n < k`. Suppose `p_n` is quasi-compact and of pure fibre dimension `d`
  (`PureFibreDimensionMorphismProperty d`: locally of finite type with every fibre of pure
  dimension `d`). Then the fibre over `y` of `D_n → V_n → M` has dimension less than `d`. The
  fibre of `D_n` is a closed subscheme of the fibre of `p_n`, which is Noetherian of dimension
  at most `d`. Suppose its image contained a nonempty open set `O`. Then `O` and the fibre
  chart of `V_k` would contain `Ω`-points with the same image in `X`, the first outside the
  threshold of `V_n` (it lies in `D_n`). `le_of_ptE_eq` would then give `k ≤ n`, a
  contradiction. The topology lemma above concludes.
- `symmetricMap_p`: `W_n → V_n → M` equals the first coordinate `W_n → U` followed by `π`,
  when `a ≫ g = h(π)`.
- `pureFibreDimension_p`: if `π : U → M` is smooth of relative dimension `d`, every `p_n`
  has pure fibre dimension `d`. `π` has pure fibre dimension `d` (Library
  `smoothPureDimension`). This is preserved by precomposition with the étale first
  coordinate (`pureFibreDimension_precomp_etale`). It descends along the étale surjective
  quotient `W_n → V_n` (`pureFibreDimension_of_precomp_etale_surjective`).
