# Full adelic determinant norm comparison

For arbitrary number fields `K` and `L` in a common universe with a
specified algebra `K → L`, `numberFieldAdeleTensorNorm` is the determinant
norm of `L ⊗[K] Adeles K` over the original full base-field adele ring.
As in `Langlands.Algebra.tensorNorm`, the factors are swapped to use the
standard algebra structure on `Adeles K ⊗[K] L`.

`numberFieldAdeleTensorNorm_eq` proves, for every tensor `z`,

`numberFieldAdeleTensorNorm K L z = adeleNorm (numberFieldAdeleTensorEquiv K L z)`.

Here `adeleNorm` is the original product of local field norms. Every
infinite and finite place is retained. No Galois hypothesis is needed.
`numberFieldAdeleTensorNormUnits_eq` gives the identical formula on actual
tensor units and full ideles, using `tensorNormUnits` and `ideleNorm`.

The proof evaluates the determinant at each base-field completion.
`adeleInfiniteEvaluation` and `adeleFiniteEvaluation` are the original
coordinate evaluations as base-field algebra maps. Coefficient naturality
of the determinant tensor norm identifies each evaluation with the local
tensor norm. The canonical completed tensor decompositions identify that
norm with the product of local norms above the chosen place, by invariance
of the determinant norm under algebra equivalence and its finite-product
formula.

`infiniteTensorEvaluation` and `finiteTensorEvaluation` check that the
completed decomposition has exactly the original full adelic tensor-map
coordinates. Tensor induction reduces these identities to pure tensors.
The pure-tensor formula uses the original completed inclusions; the
published restriction-place identities align the lower-place coordinate,
and commutativity aligns the two multiplication orders. Additivity
extends the coordinate comparison to every tensor. Finally, equality at
all places gives equality of full adeles, and injectivity of the units
value map gives the units formula.

This is internal derived infrastructure. It uses the proved completed
tensor comparisons, determinant norm naturality and product formulas.
Finite completed tensor bijectivity is supplied by the proved
`completedTensorComparison`; the infinite completed tensor equivalence is
the existing unconditional one. The pure-tensor norm formula alone would
not extend by additivity, since a norm is not additive; the implemented
argument instead applies additivity only to the comparison of coordinate
algebra maps, then transports determinant norms along those maps.

This module does not identify normalized idelic absolute values, classify
characters of a Weil restriction, or prove quotient compactness.
