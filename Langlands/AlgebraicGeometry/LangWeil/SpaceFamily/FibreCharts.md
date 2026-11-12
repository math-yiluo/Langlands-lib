# Charts of the fibres of a presheaf over a scheme

Author: Worker 75. A helper module of the proof of
`Langlands.AlgebraicGeometry.LangWeil.SpaceUniformLangWeilOfFamilyStatement`. Provenance:
internal.

## Contents

- `irreducibleSpace_of_connectedSpace` (topology): a connected space in which every point has
  a preirreducible open neighbourhood is irreducible. The irreducible component `Z` of a point
  is open. For `y ∈ Z` with irreducible open neighbourhood `O`, the set `Z` meets `O`, so
  `Z ⊆ closure O`, and maximality gives `Z = closure O ⊇ O`. A clopen nonempty subset of a
  connected space is everything.
- `overHom q` regards a scheme morphism `q : V.left → T` as a morphism `V → toOver T` over
  `S0`.
- `exists_common_point`: if points `x₁ ∈ V₁` and `x₂ ∈ V₂` of two scheme charts
  `b₁ : h_{V₁} → F` and `b₂ : h_{V₂} → F` of a presheaf have the same image in the points of
  `F`, then there are `Ω`-points `ξ₁` through `x₁` and `ξ₂` through `x₂`, with `Ω`
  algebraically closed, such that `ξ₁ ≫ b₁ = ξ₂ ≫ b₂`. The Library's
  `chartPointMap_eq_iff_sameImage₂` gives a common scheme `T` and a point `t` of `T`.
  `Ω` is an algebraic closure of the residue field of `t`.
- For `g : X → h_M` (a presheaf over `S0` mapping to a scheme), `fib g s` is the presheaf
  pullback `X ×_{h_M} h_T` along `s : T → M`. A chart `b : h_V → X` with `b ≫ g = h(q)`
  induces `fibChart g b q hb s : h_{V ×_M T} → fib g s`. `fibChart_isPullback` says that this
  is the base change of `b` (pasting of pullback squares, using that `Over.forget S0`
  preserves and reflects these pullbacks). Hence it is étale or surjective when `b` is
  (`fibChart_isEtale`, `fibChart_isSurjective`). `homOver_fibChart_fst` and
  `homOver_fibChart_snd` compute the images of points of the fibre chart in `X` and in `T`.
- `irreducibleSpace_points_fib`: let `a : h_U → X` be étale surjective with `a ≫ g = h(π)` for
  a smooth `π : U → M`, and let `K` be a field. If the points of the fibre of `g` over
  `s : Spec K → M` form a connected space (point topology), they form an irreducible space.
  The fibre chart `U ×_M Spec K` is smooth over `K`, so its local rings are domains (Library
  `smoothDomainStalks`). Every point therefore has an irreducible open neighbourhood
  (`exists_irreducible_open`). Its image in the points of the fibre is open
  (`isOpen_image_chartPointMap`) and preirreducible (continuity of the chart point map).
  The topology lemma above concludes.
- `exists_common_point_of_isOpen`: in a fibre whose points form an irreducible space, two
  nonempty open sets `W₁` and `W₂` of étale charts `b₁` and `b₂` of the fibre contain points
  `ξ₁ ∈ W₁` and `ξ₂ ∈ W₂` with values in one algebraically closed field and the same image in
  the fibre. The open images of `W₁` and `W₂` meet by irreducibility, and
  `exists_common_point` finishes.
