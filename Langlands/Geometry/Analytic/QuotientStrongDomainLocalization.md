# Full strong nested-domain comparisons and quotient localization

Author: Worker 36.

This internal construction identifies the existing full strong transport of
maps between ambient-image and nested original-domain presentations with the
independently constructed localization in the actual source-quotient category.
It uses the published original-domain strong transport, saturated composition,
full strong extensionality, and quotient domain universal property. It adds no
original-literature assertion or assumption of a strong representative for an
arbitrary quotient arrow.

`nestedDomainStrongMap` transports the full identity of the nested domain to
the ambient-image presentation. `nestedDomainStrongInverse` transports the
identity in the other direction. Their actual continuous maps insert or forget
the intermediate subspace membership. Every admissible bounded pullback is an
original restriction at the corresponding original charts, including the
pullbacks not determined by spectrum-point data.

`nestedDomainStrongMap_comp` and `nestedDomainStrongInverse_comp` identify
composition with these arrows with the existing full strong transport. For each
source chart the proof uses the identical original chart in the intermediate
presentation to compute saturated composition. Its first bounded map is the
identity restriction. Removing that identity proves the selected-pullback
equation, and full saturated strong extensionality proves the entire equality.

The forward strong comparison followed by the actual nested-domain inclusion
is the full original inclusion into the intermediate domain. After the preceding
composition equation this is equality of the literal base maps and every
original bounded restriction. The existing two strong transport round trips
prove both inverse laws for `nestedDomainStrongIso`.

`domainNestedMap_eq_strongFunctor` compares the actual quotient comparison
with the image of the constructed full strong comparison. Postcompose with the
monic quotient inclusion into the intermediate domain. The quotient comparison
triangle and the complete strong inclusion triangle give the same quotient
domain map. Monicity proves the claimed equality. Functoriality and the strong
composition formula then prove `domainNestedMap_comp_strong`: transporting a
supplied strong map and then taking its quotient image agrees with taking its
image and precomposing with the actual nested-domain comparison.

The coefficient field is complete and ultrametric and may be trivially valued.
The field, ambient-space and chart-index universes remain independent. Empty
domains are allowed. The construction uses no reducedness or point-map
faithfulness. Arbitrary quotient-family gluing, analytic-category identification
and the etale and equivariant sites remain separate obligations.
