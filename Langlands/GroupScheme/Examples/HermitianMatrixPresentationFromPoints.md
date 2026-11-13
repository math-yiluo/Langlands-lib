# Presentations from actual matrix homomorphisms

This internal adapter constructs the all-test presentation defined in `HermitianMatrixPresentation` from injective matrix homomorphisms with the exact specified image. Its proof uses codomain restriction and the elementary equivalence associated with a bijective group homomorphism. It uses no classification, rank theorem or representability construction.

The base field `k` and its separable quadratic extension `L` have a common arbitrary universe. The finite matrix index type has an independent arbitrary universe. No characteristic restriction is imposed, and the empty index type is allowed.

`Presentation.ofMatrixPoints k L H G ρ hρ_injective hρ_image hρ_naturality` takes an actual nonsingular Hermitian form `H`, a group scheme `G` over `Spec k`, and a group homomorphism `ρ T` from `(T ⟶ G.X)` into the general linear group over `SpecialLinear.WeilRoot.tensorAlgebra k L T` for every test scheme `T`. It requires injectivity for every `T`. The image hypothesis is an equivalence between the existence of an actual preimage under `ρ T` and the conjunction of the full scalar-extended Gram preservation equation and determinant one. Its naturality hypothesis is the entrywise matrix equation for every test morphism, using the actual `SpecialLinear.WeilRoot.tensorMap`.

The construction restricts each `ρ T` to the actual `tensorPoints k L H T` subgroup. The image hypothesis ensures membership and surjectivity, while the supplied injectivity gives injectivity of this restriction. `MulEquiv.ofBijective` supplies the multiplicative equivalence. The original matrix naturality equation then supplies presentation naturality directly.

`ofMatrixPoints_pointsEquiv_val` states that the underlying general linear element of the constructed equivalence is exactly `ρ T x`. `ofMatrixPoints_symm_apply` states that the inverse equivalence gives an actual preimage of each supplied subgroup element under `ρ T`.

In the existing `HermitianMatrixSplitRankStatement`, set `H := ⟨J, hJ⟩`, where `J` is its supplied invertible Gram matrix and `hJ` its Hermitian equation. The injectivity, image and naturality hypotheses of that statement then have exactly the constructor's types by unfolding the form's Gram projection. The adapter requires none of that statement's dimension, affineness or finite type hypotheses.
