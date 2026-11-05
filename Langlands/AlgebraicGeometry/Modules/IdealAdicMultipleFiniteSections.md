# Ideal multiples in families of affine sections

This internal helper applies `IdealAdicMultipleSectionImage` to families
of opens. It uses the actual inclusion of the sheafified ideal multiple,
with the base-ring action of `OModulePresheaf.ofModules`. It supplies the
product-of-sections interface needed for alternating Čech cochains.
It does not prove a uniform cohomology estimate.

The map `inclusionFamilySections` applies the actual inclusion in every
component. It is injective for every family of opens, since the inclusion
is injective on each open. If the module is quasi-coherent, the ideal is
finitely generated and every open in the family is affine, its range is
characterized by membership of each component in the corresponding
`J • ⊤`. The proof applies `range_inclusionSections` to each component;
choice then assembles the preimages. This characterization does not
require the family to be finite.

For a finite family, `range_inclusionFamilySections` identifies the
range with `J • ⊤` in the full product module. The algebraic step is that
ideal multiplication commutes with finite products of modules. One
implication follows by ideal-multiple induction and coordinate
projection. For the other implication, write a vector as the finite
sum of its coordinate vectors and use ideal-multiple induction in
each coordinate. This argument includes the empty family.

These are derived interface lemmas from the imported section-range
theorem and elementary module algebra, rather than new assertions
quoted from external literature. All universes, ideals and families
remain arbitrary subject to the displayed hypotheses.
