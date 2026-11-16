# Closed ordered root products over a commutative ring

This internal construction turns the integral coefficient recovery in
`IntegralRetraction` into morphisms of schemes. It applies to Chevalley data `D`,
any commutative base ring `R`, and any distinct list of roots that is positive
for `D.ℓ` and sorted by increasing `D.ℓ`-height.

`orderedRootAlgebra` is the polynomial algebra with one variable for each root
occurring in the list. The universal parameters `orderedRootVariables` are zero
outside the list. `orderedRootClassify` classifies the ordered product of the
root exponentials in this algebra. `orderedRootSection` sends each variable to
the corresponding recovered coefficient of the universal invertible matrix.

The composite of these algebra maps is the identity: ring-map naturality of
`integralRetrAux` reduces the claim to its coefficient recovery formula on the
universal ordered product. Thus `orderedRootClassify` is surjective.

Taking spectra gives `orderedRootMapOver` and `orderedRootRetractionOver`,
whose composite on the parameter scheme is the identity. The surjective
coordinate map proves that `orderedRootMapOver` is a closed immersion. The
affine-points formula identifies the map with the ordered root product over
every test algebra. The final two theorems specialize to the entire positive
root list and the positive root list of the opposite Chevalley data, giving the
negative product with its opposite height order.

The argument uses the Library's integral retraction, opposite data and ordered
matrix products, together with the explicit general-linear coordinate ring.
It is derived internal infrastructure for the integral Chevalley construction;
it does not assert smoothness or reductivity of an integral Chevalley model.
