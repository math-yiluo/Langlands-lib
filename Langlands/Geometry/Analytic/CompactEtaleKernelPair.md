# Clopen comparison of analytic kernel pairs

For composable morphisms `q : P ⟶ H` and `f : H ⟶ W`,
`kernelPairComparison` is the map from a kernel pair of `q` to a kernel pair
of `q ≫ f`. The two projections of the first kernel pair give the map by the
pullback property of the second. Their joint monicity makes the comparison
a monomorphism.

If `q` and `q ≫ f` are étale, base change makes the second projection of
each kernel pair étale. Their compatibility and étale right cancellation
then make the comparison étale. An étale monomorphism is injective on
points because compatible points lift to its self-pullback, which is the
identity square of its source. Together with openness of étale maps this
gives an open embedding of underlying spaces.

If `P` is compact Hausdorff and `H` is Hausdorff, the kernel pair of `q` is
compact by the compact étale pullback construction. Its image in the kernel
pair of `q ≫ f` is therefore clopen when the latter space is Hausdorff.
The argument applies over every complete ultrametric normed field, with
independent field and space universes.
