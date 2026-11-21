# Integer and residue automorphisms of cyclic extensions

This module develops descent data for the unit fundamental lemma using the
Library's canonical integer and residue rings. It equips the published actions
`Ramification.Padic.integerAutHom` and `Ramification.Padic.residueHom` with
relative algebra structure. The integer action fixes the image of the base
integer ring by the field automorphism's scalar law. Surjectivity of residue
reduction gives the scalar law on the base residue field.

The published `IsCyclicAlgebra.isGalois` gives Galoisness from the fixed-field
hypothesis. For an unramified extension, the published injectivity of the spectral
residue action transports through the comparison with the canonical residue
field. An integer lift of a primitive residue element then has distinct
reductions under the powers of the given cyclic generator. Extending the
maximal ideal along the relative integer map gives the extension maximal
ideal by the relative index one case of
`map_maximalIdeal_of_ramificationIndex_eq_mul`.
