# Ampleness near a proper fibre from a generating power-section system

This internal module introduces `FibrePowerSectionSystem p L s` for an actual
line bundle `L` on `X`, a morphism `p : X ⟶ S`, and a point `s` of `S`.
Its data are a positive degree and finitely many sections of that tensor power,
indexed by `Fin (dimension + 1)`. Their whole generation opens cover `X`, and
the inverse images of those opens in the actual scheme-theoretic fibre at `s`
are affine. Schemes range over every universe `u`.

For a proper `p`, `exists_ample_neighbourhood` proves that the fixed bundle `L`
is ample on the inverse image of an affine open neighbourhood of `s`.
`ampleNeighbourhood` chooses that neighbourhood together with the stated proofs.
No noetherian or flatness premise is needed for this geometric implication.

The implemented proof regards the chosen tensor power as a line bundle and
uses the sections to define its relative linear-system morphism. The affine
fibre generation opens make this morphism finite after shrinking the base to
an affine open `V`, by `LinearSystem/ProperFibre`.

Put `Q` equal to the inverse image of `V` in relative projective space and
`U` equal to its inverse image in `X`. The structure-morphism identity gives
`U = p⁻¹(V)`. Each coordinate chart of `Q` is affine because the composite
`Q ⟶` integral projective space is affine, using the existing
`isAffineHom_preimage_ι_toIntegral`. The finite restricted linear-system map
has affine inverse images of these charts. The whole-coordinate-preimage
identity identifies them with the restrictions to `U` of the original section
generation opens. Pulling back the original power sections with
`LineBundle.pullbackPowSection` preserves those whole opens and the positive
degree. They therefore witness the pointwise section condition for ampleness
of the original restricted bundle. Properness makes `p⁻¹(V)` quasi-compact.

The provenance is internal: all inputs are the published actual sheaf,
section, relative linear-system, and affine/proper morphism APIs and the
geometric prerequisites supplied in this task. This result assumes a
generating section system on the total space; constructing one from fibre
ampleness still requires the separate section-lifting argument. It does not
assert the unconditional proper-fibre ampleness spreading target.
