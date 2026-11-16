# Fppf generation by an open unit neighbourhood

Let `G` be a reductive group scheme over an arbitrary scheme `S`, and let `Ω : P → G.X` be an open immersion whose image contains the unit section. Suppose that for every test scheme `Z` and every morphism `p : Z → P`, the point `p ≫ Ω` is fppf-locally in the ordinary abstract commutator subgroup. Then every point of `G` has the same local commutator membership.

The proof uses the published arbitrary-base results `ReducedBaseSmooth.smooth_tensorHom_comp_mul` and `range_tensorHom_comp_mul_eq_univ`. Reductivity supplies the smooth connected residue fibres; the open neighbourhood is smooth over `S`. Thus multiplication of two copies of `P` is a smooth surjective morphism onto `G`. Pulling that morphism back along the given point gives a single surjective flat locally finitely presented refinement of its test scheme. On the refinement the point is a product of two values from `P`, each locally a commutator by hypothesis; product closure and fppf-cover descent finish the proof.

This is an internal reduction. It imposes no affineness or quasi-compactness assumption on the base, test scheme or cover, and assumes no relative derived-group existence statement.

`openCellCommutatorCover` chooses the resulting cover, and `openCellCommutatorCover_mem` records the abstract commutator membership of the restricted point on every member. These conclusions retain the open-cell local-membership hypothesis explicitly.
