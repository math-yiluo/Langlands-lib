# Injectivity of ordered sharp and full chamber products

This internal supporting development proves injectivity for the four existing
ordered negative/central/positive maps: sharp chamber, sharp facet, full chamber
and full facet. It keeps the Dynamic ordered root product statement as an
explicit premise and proves no exact range or Iwahori decomposition assertion.
It also equips the full ordered chamber map with an embedding whose underlying
function is definitionally the original `orderedIwahoriChamberProduct`.

The proof combines the existing injectivity within each sign with the published
three-factor uniqueness theorem. The positive pairing of each root places its
actual relative root subgroup in the Dynamic unipotent subgroup. Each actual
block lies in its root subgroup, by the published doubled-root block identities.
Closure of a subgroup under finite ordered products places the product of the
blocks in the Dynamic unipotent group. Using the negative cocharacter gives
the opposite containment.

The general map-restriction lemma lifts these two injective maps to the
corresponding unipotent subtypes. Three-factor uniqueness distinguishes both
unipotent images and the central coordinate. Injectivity within each sign
then distinguishes every original block coordinate.

The sharp maps retain `D.sharpCentralizer {x}`. The full maps retain the actual
`P.centralizerZero = Z(F)^0`, mapped by the actual centralizer inclusion.
Monicity of its representation gives injectivity of that central map, and
the existing representation property gives centralization. No equality of
sharp and full factors is used.

The chamber results cover both Boolean depths, and the facet results retain
negative depth `0+` and positive depth `0`. All orders separately within each
sign and the empty index set are covered at arbitrary universe `u`. The facet
subset may be empty. These injectivity claims do not need chamber membership,
genericity, apartment axioms, or the facet sign condition.

The provenance is the internal argument above using the established
`RootSubgroupPositive`, `ChamberOrderedInjective` and `ChamberProductInjective`
interfaces. This unit makes no further literature claim. The Dynamic ordered
product premise, every exact range, the central and normalizer comparisons
and the complete target remain separate obligations.
