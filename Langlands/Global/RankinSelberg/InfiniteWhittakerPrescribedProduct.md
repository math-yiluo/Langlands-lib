# Prescribed archimedean factors for the infinite Whittaker residual

`HasPrescribedInfiniteWhittakerProduct` records a product of specified real and complex functions for the infinite residual of a global Whittaker function, with scalar `κ`. `exists_prescribed_infiniteResidual_product` assumes the one-place slice comparisons in `ModelData`, finite additive support in `S`, canonical finite characters and finite reference vectors normalized by the given local functionals. When each specified function is in the range of its slice model map, the theorem chooses an infinite pure tensor with that residual product and proves `κ ≠ 0`.

The proof selects one vector above each prescribed function, applies the normalized product for the fixed finite references and splits the product over real and complex places. The nonzero scalar comes from the published slice product theorem. The diagonal inclusion used in unequal ranks commutes with taking each infinite component and with setting the finite component to the identity. The proof compares entries of the padded matrices under the corresponding ring maps.

The prescribed product implements the infinite part of the ordinary Euler factorization in Cogdell (2004), §4.1, printed pp. 219–220 (registered PDF pp. 222–223).
