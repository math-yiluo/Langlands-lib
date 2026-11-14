# Transport of actual row eigenvectors through an orthogonal Morita comparison

This internal derived helper transports a supplied split eigenvector law
through a supplied `OrthogonalMoritaComparison`. It uses the actual group
points and inverse-right row actions to establish membership in
the actual extended all-test cocharacter weight spaces.

`OrthogonalMorita.scalarRow` extends an element of
`L tensor_K (Fin m -> D)` along its coefficient factor to any commutative
`L`-algebra `S` with compatible `K`-algebra structure.
`rowEquivOver_self` identifies the canonical comparison extended to `L`
with the original comparison, and `rowEquivOver_scalarRow` shows that the
extended comparison carries a coefficient-extended tensor row to the
coefficient extension of its original image.

`mem_cocharacterWeightSpaceOver_of_tensor_eigen` takes the actual tensor
row eigenvector equation over every such `S` and every `S`-valued point
of the original multiplicative group. It specializes this law to the
relative Laurent test algebra `L tensor_K LaurentPolynomial K` and its
universal multiplicative point. The row/tensor distribution equivalence
identifies that equation with the defining universal equation of the
actual extended weight space.

`rowBasis_mem_of_split_eigen` assumes that a supplied split basis satisfies
the inverse-right eigenvector law for the image of each original
cocharacter point under the actual Morita group comparison. Its
eigenvalue is the actual coefficient unit raised to the given integer
weight `w i`. Using the comparison's `intertwines` law and its injective
extended row equivalence proves that each pulled-back copy basis vector
belongs to the extended weight space of `w i`.

No comparison or split eigenbasis is constructed here. The split
eigenvector equation, including its compatibility with the actual
cocharacter points and integer exponents, is an explicit hypothesis.
This module does not identify the type-D characters or their lattice
pairings, or prove that the host hypotheses supply that equation.
The argument is derived from the existing row comparison, its coefficient
naturality, the product-basis formula and the Laurent criterion, without
any additional literature assertion or characteristic restriction.
