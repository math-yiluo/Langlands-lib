# Tensor evaluations on compact block products

The source is a compact-finite representation of a group `K`. A group homomorphism `j` maps the product of the block groups `J i` to `K`, and `ℓ` is a scalar coefficient. The intended application uses the block diagonal embedding. For each block the input includes a linear slice whose compact evaluations equal the translates of `ℓ` through that block. Each block evaluation map `e i` is injective.

For a fixed vector and a fixed right compact argument, all coordinate slices of the scalar coefficient on the compact block product are images of vectors in the same finite-dimensional orbit span. The Library's `mem_prodSpan` theorem expresses the coefficient as a sum of products of such slices. `indexedEvaluation_injective` gives the unique algebraic tensor representing it. This defines `evaluation`, a linear map at every compact argument.

`evaluation_right` compares right source translation with multiplication of the argument. Given block representations `σ i` satisfying `e i (σ i p v) q = e i v (q * p)`, `evaluation_left` identifies multiplication of the argument on the left by `j p` with the tensor of those block actions. `evaluation_separates` tests the identity of the block product and transfers separation by the original compact coefficient to separation by the tensor evaluations.

This is an internal algebraic construction for the compact realization of normalized induction. It uses the finite-dimensional orbit argument of `RealLeviProducts` and applies to both real and complex compact groups with their respective block slices. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the compact model and the role of scalar Levi evaluations.
