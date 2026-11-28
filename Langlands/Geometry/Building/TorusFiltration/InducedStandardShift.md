# First congruence of the induced standard filtration

`inducedStandardCongruence` proves that for any smooth model of the
standard depth-\(r\) subgroup of an induced torus, the generic image of the
reduction kernel is the standard depth-\(r+1\) subgroup. The ring is
`fixedFieldIntegers F` and the field is `inertiaFixedField F`.

`inducedTorusWeilDecomposition` identifies the torus with the Weil
restriction of the multiplicative group for a product of intermediate
fields of a finite Galois splitting extension. Reindexing and mapping
each field into the separable closure gives the coefficient algebra for
`InducedTorusShallow.depthModel`. Changing the model's generic
identification transports its integral points and congruence subgroup
by the induced map on rational points.

At positive depth, `localTorusFiltrationAtSplitting_eq_geometric_of_induced`
identifies the standard term with the geometric character subgroup.
The coefficient model realizes that subgroup by
`depthModel_integralPoints_positive`, and geometric character congruence
is functorial in both directions of the torus isomorphism.
At zero, `inducedTorusIwahori` identifies the standard term with the
character valuation kernel. Integral points lie in this kernel by
`IntegralModel.integralPoints_le_characterValuationKernel`. Conversely,
`WeilGm.product_coordinate_valuation_eq_one_of_mem` gives unit valuations
in the Weil coordinates over the splitting extension. The map on rational
units acts by the coefficient algebra equivalence, as follows by applying
`WeilGm.congrIso_hom_points` and checking the induced tensor map on pure
tensors. These unit valuations therefore give an integral point of the
depth-zero coefficient model.

`depthModel_congruenceSubgroup` now computes the shift on the transported
model. If a second smooth model has the same integral points, the smooth
homomorphism extension gives maps in both directions extending the generic
identity. Their compatibility with reduction gives the same first
congruence subgroup on the two models.

The calculation uses the induced-torus description in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition B.3.6(1), printed
pp. 658–659, PDF pp. 689–690, and realizes the congruence shift of
Definition B.5.3. The smooth extension is Corollary 2.10.10.
