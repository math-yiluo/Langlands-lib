# The canonical integer-localization base of ordinary level moduli

This is internal infrastructure for the existing full category `LevelBase n`.
It constructs its canonical maps to `Spec ℤ[1/n]` without changing the object
predicate or the actual scheme morphisms in that category.

`localizationToGlobalSections S` is the unique ring homomorphism from
`Localization.Away (n : ℤ)` to `Γ(S.obj, ⊤)` extending the integer map.
Its construction uses the existing proof that the natural-number cast of `n`
is a unit in the global sections. The global-sections/spectrum adjunction
then gives `toLocalizationSpec S`.

The proof of `localization_hom_ext` applies the same adjunction and uniqueness
of maps out of a localization. The induced maps agree on the integers because
there is only one unital ring homomorphism from the integers to a fixed ring.
This uniqueness holds for an arbitrary universe-zero scheme, without local
noetherianity or an invertibility premise. Existence is only asserted for
objects where the required unit is present. In particular the argument also
covers the zero localization at `n = 0`.

`eq_toLocalizationSpec` identifies any other supplied structure map with
the constructed one. `toLocalizationSpec_naturality` says that every actual
scheme morphism between the existing test objects is automatically over this
base. It does not impose a condition on the morphisms.

`localizationSpec n` constructs the base affine scheme as a `LevelBase n`
object: localization preserves the noetherian property of the integer ring,
and the element inverted by the localization is a unit. The canonical
global-sections isomorphism transfers this last fact to the spectrum.
`localizationSpecIsTerminal n` packages its terminal universal property.

Finally, `toOverLocalization n` constructs the functor to schemes over this
affine base, and `overHomEquiv` identifies every Hom type there with the
original Hom type in `LevelBase n`. These are actual scheme morphisms,
including on nonreduced tests.

The provenance is internal: the exact base category is already published in
`PolarizedFiniteLevel.Base`, and the construction uses Mathlib's localization,
global-sections/spectrum adjunction and full subcategory machinery. This
module proves no moduli representability, constructs no universal family,
and adds no hypothesis to the ordinary moduli functor.
