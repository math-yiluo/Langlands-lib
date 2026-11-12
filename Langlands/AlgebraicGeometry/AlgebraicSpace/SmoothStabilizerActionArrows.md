# The arrow scheme of a group action and its smooth projections

This internal helper supports the proof of `SmoothStabilizerActionQuotientStatement`. It
proves that the arrow scheme of a group action has smooth projections when the
stabilizer is smooth. It follows the first step of the Stacks Project's proof of
Proposition 101.28.9 (Tag 06QJ). There the arrow space `R = (G × V) ×_{V × V} (G × V)`
is identified with a base change of the stabilizer, so its projections inherit the
stabilizer's flatness, here smoothness. The proof is a direct computation with points
of schemes over `S`.

Let `G` be a group scheme over a scheme `S`, acting by `a` on a scheme `V` over `S`.
Points are morphisms from a test scheme `T` over `S`. `T`-points of `G` form a group
under the categorical group structure. `a.act g v` is the action on points, and
`a.act g v = lift g v ≫ a.hom`.

- `graph a` is the action graph `G × V → V × V`, `(g, v) ↦ (g.v, v)`. This is the map
  `lift a.hom (snd G.X V)` used in the target statement.
- `stabilizer a` is the base change of `graph a` along the diagonal
  `lift (𝟙 V) (𝟙 V)`. `stabilizerProj a` is its projection to `V`. This is the morphism
  whose smoothness the target statement assumes.
- `act_fst_snd` says that the action map at a point `m` of `G × V` is the action of its
  first component on its second component.
- `comp_graph_eq_iff` says that two points of `G × V` have the same graph image exactly
  when they have the same action image and the same second component.
- `stabilizer_fst` and `stabilizer_act` describe a point of the stabilizer scheme. It
  is a point `(h, v)` of `G × V` with `h.v = v` and with `v` its image in `V`.

For a pullback square `h : IsPullback r s (graph a) (graph a)`, a point of `R` is a pair
`(g, v)`, `(g', v)` with `g.v = g'.v` (`arrow_eq`). Then `g' g⁻¹` fixes `g.v`
(`act_arrow`). `arrowToStabilizer h` is the resulting map `R → stabilizer a`,
`((g, v), (g', v)) ↦ (g' g⁻¹, g.v)`.

`isPullback_arrowToStabilizer` proves that the square formed by `arrowToStabilizer h`,
`r`, `stabilizerProj a` and the action map `a.hom` is a pullback. So the first projection
`r` is the base change of the stabilizer projection along the action map. The proof
checks the universal property of the pullback cone. A point `k` of the stabilizer, with
group component `h₀`, and a point `(g, v)` of `G × V` with `h₀` fixing `g.v` lift to the
point `((g, v), (h₀ g, v))` of `R`. The two factorization identities and uniqueness are
computed componentwise with the group laws for points.

`smooth_arrow_fst` concludes that `r` is smooth when `stabilizerProj a` is smooth.
Smoothness of schemes is stable under base change, and the square is mapped to schemes
by the forgetful functor from `Over S`. `smooth_arrow_snd` obtains smoothness of `s`
by applying the same result to the flipped pullback square.
