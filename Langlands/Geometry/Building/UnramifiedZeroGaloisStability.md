# Galois stability of the torus contribution

This module proves that, for every nonarchimedean local
field `F : Type u`, every group scheme `G` over `F`, every supplied
`UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G)`, every
`F`-automorphism `σ` of the maximal unramified extension, and every
`t ∈ E.torusIwahori`, the conjugate of the image of `t` belongs to
`E.zeroPoints`. No additional reductivity premise on `G` is required; the
supplied datum carries its own structural hypotheses.

The construction `UnramifiedZeroDatum.galoisTransport` and its preservation of
the torus norm subgroup are already in the Library. The new proof first computes
the underlying morphism of the transported torus inclusion. A private lemma
computes the first projection of the pullback of an arbitrary morphism in an
over category. Composing that projection with the canonical ambient descent
formula proves `galoisTransport_i_fst`. The projection criterion for actual
coefficient conjugation then gives `galoisTransport_map_point`.

Next, `galoisTransport_section_mem_torusIwahori` applies the published norm
transport inclusion to the changed section of `t`.
`galoisTransport_map_section_mem_zeroPoints` puts its image in the zero subgroup
of the transported datum. Finally,
`rationalConjugate_torusIwahori_mem_zeroPoints` substitutes the actual-point
comparison and applies `unramifiedZeroPointsIndependence` to identify that zero
subgroup with the original `E.zeroPoints`. These separate lemmas keep the
kernel's conversion checks small.

`UnramifiedZeroTorusGaloisStabilityStatement` packages exactly the torus
membership conclusion proved pointwise above. The provenance is internal and
derived from the named Library constructions, projection formulas and
independence theorem. This module does not prove stability of the simply
connected image, the complete clause 2, or descent to `F` in clause 3 of
`UnramifiedZeroDescentStatement`.
