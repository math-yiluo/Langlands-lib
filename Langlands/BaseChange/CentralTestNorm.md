# The norm on scalar centers for local base change

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), §I.2.9, printed p. 22 (PDF p. 30), uses the
scalar norm image in the lower group and the full scalar center in the upper
group. The upper character is pulled back along the field norm. The same
section describes the choice factor by factor at a product of places.

Retained source `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.

`Langlands.GeneralLinear.scalarCenterContinuousEquiv` identifies the units of
a topological commutative ring with the full center of its general linear
group in positive rank. The forward map is the scalar homomorphism. The
inverse reads one diagonal entry, and its inverse-unit coordinate reads the
corresponding entry of the inverse matrix. For a Hausdorff coefficient ring
the center is closed, so the scalar map is a closed embedding.

`Langlands.BaseChange.scalarNormSubgroup` is the image of the determinant-norm
subgroup under the scalar map. Its centrality gives a normal-subgroup instance
for the actual quotient. For finite extensions of the supplied p-adic fields,
`isClosed_scalarNormSubgroup` uses closedness of the norm subgroup in the field
units and the closed scalar embedding. `scalarCenterNorm` composes the inverse
scalar identification upstairs with the continuous field norm and the lower
scalar map, with codomain restricted to the scalar norm image. On the scalar
matrix of a unit `a` it returns the scalar matrix of `N(a)`. Every element of
the lower subgroup has this form, so the map is surjective. The norm input
works for finite extensions, including the cyclic extensions in the cited
construction, and the two fields can have independent universes.
