# Real approximation reduced to connected reductive groups

`realApproximationReductiveReduction` proves the exact proposition
`Langlands.GroupScheme.RealApproximationReductiveReductionStatement`. The
antecedent is real approximation for every connected reductive group over `ℚ`.
The conclusion retains every smooth connected affine group over `ℚ` and the
actual evaluation topology on its real points.

For such a group `G`, the published characteristic-zero Levi decomposition gives
a connected reductive group `L`, a quotient homomorphism `p : G → L`, and a
homomorphism section `j : L → G` with `p ∘ j = id`. Its actual scheme-theoretic
kernel `U` is smooth, connected and unipotent. The kernel pullback makes `U`
affine. Over the perfect field `ℚ`, the published unipotent split theorem supplies
a finite split series, and the published split-unipotent affine-space theorem
identifies `U` with an affine space.

The elementary evaluation-topology density theorem proves real approximation
for this affine space and transports it to `U`. The reductive antecedent gives
the assertion for `L`, so product density gives it for `U × L`. Smoothness gives
the local finite-type assumptions of the product-continuity theorem.

The underlying scheme morphism
`f : U × L → G`, `(u,l) ↦ u j(l)`, is surjective on actual real points. For a real
point `g`, put `l = p(g)` and `a = g j(l)⁻¹`. The section identity implies
`p(a) = 1`, so the kernel pullback gives a real point `k` of `U` with image `a`.
The pair `(k,l)` maps to `g`. The density transport theorem for a
morphism surjective on real points finishes the proof.

The construction of kernel-times-section multiplication uses the elementary
group calculation also present in the shared connected-group-unirationality
draft. Here the kernel universal property is applied directly on real points.

This proof implements the final Levi and affine-space step of Milne,
*Algebraic Groups* (2017), Theorem 25.70, with approximation for connected
reductive groups as its explicit antecedent.
