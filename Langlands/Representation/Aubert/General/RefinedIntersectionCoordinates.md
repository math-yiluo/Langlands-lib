# Coordinates on refined radical intersections

This internal prerequisite concerns literal subgroups of any group `A`. Its topological conclusions use the subtype topologies from `A`. It is derived from the published unique-factorization and continuous-coordinate constructions, with no original-literature claim.

For an original semidirect decomposition `P = M U`, `IsSemidirectDecomposition.ofSubgroupProduct` proves a semidirect decomposition `R = B W` whenever `B ≤ M`, `W ≤ U`, `R` normalizes `W`, and the displayed product is an equality of subsets of `A`. It first proves both inclusions into `R`. Existence follows from the subset product; uniqueness follows from the original Levi projection. `projection_eq_of_subdecomposition` identifies the refined projection with that original projection on ambient points. Its continuous version restricts the original continuous projection to the two subtype groups. No topology is needed for the algebraic assertions; projection continuity alone needs only a topological space on `A`.

`RefinedIntersection.eq_mul` starts with

- `R = (M ∩ V) U`;
- `S = (N ∩ U) V` and `S ≤ Q`;
- `U ∩ Q = (U ∩ N)(U ∩ V)`.

It proves `R ∩ S = (M ∩ V)(U ∩ Q)`. Indeed `V ≤ S` follows by setting the first factor to one, and the given radical-parabolic product gives `U ∩ Q ≤ S`. Decomposing an intersection point as `b u` then places `u` in `S` and hence in `Q`; the converse multiplies the two displayed factors. `eq_triple_mul` substitutes the final displayed product. All products are subset products in the original ambient group, with the stated order.

Given semidirect decompositions `d : P = M U` and `e : Q = N V`, `left_le_parabolic` derives `R ≤ P`. The outer decomposition of `R ∩ S` has factors `M ∩ V` and `U ∩ Q`: its radical is normalized because the intersection lies in `P ∩ Q`, and `P` normalizes `U`. The inner decomposition of `U ∩ Q` has factors `U ∩ N` and `U ∩ V`: its radical is normalized because elements lie in `U ∩ Q`, and `Q` normalizes `V`. Both decompositions inherit uniqueness from `d` or `e` through `ofSubgroupProduct`.

If the original two projections are continuous, `continuous_outer_projection` and `continuous_inner_projection` prove continuity of the new projections by restricting them. When `A` is a topological group, `RefinedIntersection.coordinates` composes the two published multiplication homeomorphisms to give

`(M ∩ V) × ((U ∩ N) × (U ∩ V)) ≃ₜ R ∩ S`.

`coordinates_apply` states that its forward map is exactly `b * (a * c)` in `A`. There is no closedness, local compactness, countability, field, reductivity or characteristic hypothesis here. The algebraic product premises remain explicit; the rational-point application must derive them separately. This module proves neither a squared-modulus identity nor the representation-theoretic geometric expansion.
