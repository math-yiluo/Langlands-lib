# Actual SU3 rational images and parabolic elementary subgroups

This internal construction concerns fields `k` and `L` in an arbitrary common universe, with a separable quadratic extension `L/k`. There is no characteristic restriction. Its source is the actual closed group scheme `SchemeModel.groupScheme k L`, and its rational points are morphisms from the identity test scheme.

The tensor coefficient equivalence at `baseAffineTest k` transports the original upper matrices entry by entry. Its induced parameter equivalence is surjective. Consequently every original `rationalUpper` point becomes an actual `upperPoints` point after changing to the affine base test. Pullback along the inverse identity-test isomorphism proves membership in the actual `upperFunctor` at the identity test. The previously constructed polynomial contraction therefore proves `rationalUpper_range_le_dynamicUnipotent`.

The actual `weylPoint` is the inverse rational matrix image of the determinant-one anti-diagonal Weyl matrix. Injectivity of the rational matrix equivalence and the original definition of `oppositeEmbedding` prove that its conjugation takes `rationalUpper x` to `rationalLower x`. Normality and the proved generation by both root families give `eq_top_of_normal_upper_range`.

For any actual homomorphism from this SU3 scheme to a group scheme `G`, normal containment of the dynamic subgroup for the composed cocharacter implies containment of the entire rational image. In particular, when `G` is connected reductive, the proved dynamic-to-geometric-parabolic-radical comparison supplies this containment in the actual `parabolicElementarySubgroup G`. The proof requires connected reductivity only of the target.

These are derived internal results using the published matrix, point, contraction and parabolic-radical constructions. No external classification or local-field theorem is invoked. Smoothness and reductivity of the source, general rank-one classification, and unrestricted local Kneser–Tits remain separate obligations.
