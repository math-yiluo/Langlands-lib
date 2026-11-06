# Conjugation and coroot corrections for actual reflection translations

This module proves consequences of the published actual root-group and
valuation-data interfaces. Its provenance is internal: it develops the actual
translation images of `ReflectionTranslationLattice` without adding premises to
`SimplyConnectedReflectionTranslationStatement`.

For supplied `B : ValuationBuildingData G` over a nonarchimedean local field in
an arbitrary universe, `conjugate_oppositeFactorPair` simultaneously conjugates
the root point and the two opposite factors by an actual normalizer point.
Root-group conjugation transports their roots by the Weyl action, and closure
of the normalizer under multiplication and inverse gives the normalizing
product. `reflectionElement_conjugate` identifies its representative by the
group identity for conjugation of a product.

The instance `reflectionNormalizer_normal` shows that the subgroup generated
by all actual opposite-pair representatives is normal in the actual normalizer.
Conjugation takes each generator to another such generator: the actual Weyl
action preserves relative roots, conjugation preserves nonidentity, and the
preceding pair transport identifies the representative. The universal property
of subgroup closure extends this containment from generators.

For an actual centralizer point `z`, a nonidentity point `g` of the root group
of `a`, and an actual opposite pair `hp` of `g`,
`rootForm_translation_smul_coroot_mem_reflectionTranslationLattice` proves

```text
rootForm(a, reducedCentralizerTranslation(z)) • reflectionCoroot(g,hp)
  ∈ reflectionTranslationLattice.
```

The proof conjugates `g` and its opposite factors by `z⁻¹`. The Weyl action of
the centralizer is trivial, so this is a second pair for the same root. Axiom
V6, which belongs to the supplied data, says that the two root values differ
by `rootForm(a, reducedCentralizerTranslation(z))`. The published same-root
correction theorem therefore realizes the displayed full translation vector.

Finally, `reflectionTranslationLattice_eq_of_no_relativeRoots` proves equality
of the images when the actual relative-root set is empty. Every reduced
translation is then zero, by separation by the actual root coordinates.

The coroot-coordinate result does not assert that the original translation
belongs to the reflection image. These lemmas do not establish the general
simply connected translation-image equality, any saturation property, or a
primitive integral realization theorem. No apartment axioms, opposite-pair
existence, or simple connectedness are assumed.
