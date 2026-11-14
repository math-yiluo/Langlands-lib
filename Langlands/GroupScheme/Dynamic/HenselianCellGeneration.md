# Integral section generation from dynamic open cells

This internal derived unit combines the published arbitrary-base dynamic
opposite cell, its parabolic product isomorphism, the translated-cell
intersection cover, and smooth section existence over strictly Henselian
local rings. All declarations retain arbitrary universe `u`.

The shared [BaseTripleCell](BaseTripleCell.md) theorem
`Dynamic.isOpenImmersion_tripleCellMultiplication_overBase` extends the
existing field triple-cell theorem to any base scheme. For a smooth
affine group and any actual representatives of the negative dynamic
radical, the dynamic centralizer, and the positive dynamic radical,
their ordered multiplication is an open immersion. Its proof replaces
the last two factors by a representative of the dynamic parabolic from
`dynamicBaseRepresentability`, through the actual parabolic product
isomorphism, then applies `dynamicBaseOppositeCell`.

For a Henselian local ring `R` with separably closed residue field, take
a smooth group scheme `G` with geometrically irreducible fibres and an
open immersion `j : C → G` from any scheme over `R`, with a section `e`
mapping to the identity. `CellGluing.cellSectionImage` is the image of
the actual `R`-sections of `C` in `G(R)`. The source `C` need not be a
group scheme.

`exists_cellSection_product` expresses every actual group section as a
product of two sections from this cell. The translated-cell intersection
`splitOpen j g` is smooth and surjective over `Spec R`, by the published
intersection-cover theorem and smoothness of the ambient group.
`HenselianParabolicCovering.nonempty_ringPoint_of_smooth` supplies an
actual section of this intersection. Its auxiliary point `h` lies in
the cell, and so does `g h⁻¹`; taking their cell coordinates gives the
ordered product `g = (g h⁻¹) h`. No surjectivity on residue points is
assumed as additional data.

`cellSectionImage_mul_self` records that this image multiplied by itself
is all of `G(R)`. `eq_top_of_cellSections` consequently proves that any
subgroup containing all actual cell sections is the whole section
group.

`Dynamic.eq_top_of_dynamic_section_ranges` applies this fact to the
actual arbitrary-base dynamic triple cell. Any subgroup of `G(R)`
containing the section images of the negative radical, centralizer and
positive radical is the whole group. Multiplication of a cell section
is the specified ordered product of these three original factor
sections.

The construction requires neither a discrete valuation nor a fraction
field, compactness, finite index, or a reductive ambient group. It
retains geometric irreducibility as an explicit hypothesis. It does
not construct an integral split torus or identify dynamic factors with
root-model images. Those comparisons remain separate obligations for
an application to the unramified neutral-model target.
