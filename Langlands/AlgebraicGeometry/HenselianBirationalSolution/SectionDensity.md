# Choosing sections over a strictly henselian discrete valuation ring

`exists_section_lift_mem` proves that for a smooth surjective `Y ⟶ Spec R`,
a fibrewise dense open in `Y ×_R P` contains the lift of a specified point of
`P` under some section. The image of the open in the fibre of `P` gives an
open subset of the corresponding fibre of `Y`, using openness after the
residue-field base change. This subset contains a generization in the fibre
of each point of that fibre. Once a section hits it, the fibre product has
a unique point with the section coordinate and the specified point of `P`.

For the closed point, `exists_section_closedPoint_mem` uses the density of
rational points of the smooth special fibre over the separably closed
residue field and lifts a rational point by smooth Hensel lifting. These
are the assertions of BLR, *Néron Models*, §2.3 Proposition 5, p. 47.

For the generic point, choose a generic point of a special-fibre component.
Its local ring is a DVR by smoothness, so it has a unique proper generization
`ξ`, lying over the generic point of the base. The special-fibre point lies
in the closure of section specializations and hence in the closure of their
generic points. On an affine Noetherian neighbourhood, take an irreducible
component of that closure which contains the special-fibre point and meets
the set of section generic points. Its generic point lies over the generic
point of the base and so equals `ξ`. Since `ξ` has no proper generizations
it belongs to the prescribed fibrewise dense open in `Y`, which therefore
meets the set of section generic points. This supplies the section choice
used in the local constructions corresponding to BLR §5.3 Lemmas 6 and 8,
pp. 125–126 and 127–128.
