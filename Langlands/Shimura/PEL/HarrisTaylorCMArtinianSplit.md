# Artinian test lifting with a section

`CMLevelArtinianFieldTargetLiftingStatement` is the restriction of the existing
`CMLevelArtinianLiftingStatement` to field target rings. It retains the actual
test maps over the CM test base field `F`, all their admissibility data and
the entire normalized class presheaf at each small level.

`surjective_specTestMap_of_section` applies to noetherian test rings. A section
of the ring map compatible with the given structure morphism gives a retraction
on spectra over `Spec F`. Functoriality gives a section of restriction on
the normalized classes.

For `cmLevelArtinianFieldTargetLifting`, the source maximal ideal equals the
kernel and has square zero by the elementary-thickening hypothesis. The given
structure morphism of spectra determines the `F`-algebra structures on the test
rings. A transcendence basis and separability in characteristic zero give
formal smoothness of the field target over `F`. This supplies the
ring section for `surjective_specTestMap_of_section`, including for residue
fields of infinite transcendence degree.
