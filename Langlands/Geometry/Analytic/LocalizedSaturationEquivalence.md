# Actual comparison of the constructed localizations

This is an internal comparison of the actual original compatible and
saturated atlas localizations. The field is a complete ultrametric normed
field, allowing trivial valuation. Both categories and their full
quasi-isomorphism classes are the previously constructed categories of
actual affinoid atlases and their bounded pullback families. Original
maps satisfy the explicit local-domain compatibility law. A full
quasi-isomorphism retains an ambient homeomorphism and full affinoid-test
representation at every admissible chart pair.

`saturationLocalizer` uses the existing actual saturation functor and
the proved preservation of this class from
`CompatibleStrongQuasiIsomorphisms`. It is a Mathlib
`LocalizerMorphism` between these particular morphism properties.
The original ambient universe is `v`; its chart-index universe `w`
remains independent, while the saturated target has index universe `v`.

`localizedSaturationFunctor` descends the composite of actual saturation
and the saturated quotient functor through the original compatible
quotient. The inversion premise follows from actual class preservation
and inversion by the saturated quotient. Its strict descent equation
proves that the square of quotient functors commutes. This also supplies
the `CatCommSq` instance used in the equivalence argument.
The object equation sends an original quotient object to the quotient
of its actual enlargement. The map equation recovers exactly the
saturated quotient image of the complete extended bounded family.

`quasiIsomorphisms_le_map_saturationFunctor` uses the common index
universe `w = v`. It proves that every saturated full quasi-isomorphism
lies in the image of the original class up to an isomorphism in the arrow
category. Here Mathlib's `MorphismProperty.map` means this image up to
arrow isomorphism.

For a saturated full quasi-isomorphism `f : S ⟶ T`, form the actual map
`F = S.saturationIso.hom ≫ f ≫ T.saturationIso.inv` between the
enlargements of `S.presentation` and `T.presentation`. The two comparison
maps have the previously proved full quasi-isomorphism properties
`isQuasiIso_directFromSaturation` and
`isQuasiIso_directToSaturation`. Actual saturated multiplicativity
therefore proves that `F` is a full quasi-isomorphism.
Its constructed `originalRestriction` is a full original compatible
quasi-isomorphism by the proved reflection theorem.
The equality `saturationExtension_originalRestriction` recovers the
entire bounded family of `F`. Together with the inverse law of
`T.saturationIso`, it proves the commutative square whose endpoint
isomorphisms are `S.saturationIso` and `T.saturationIso`.
`Arrow.isoMk'` constructs the required arrow isomorphism.
Thus the class image is established with actual bounded-map recovery,
without assuming a separate invariance-under-isomorphism premise.

The existing saturation functor is an equivalence in this same index
universe by `SaturatedComparisonEquivalence`. This fact and the just-proved
class image inclusion meet Mathlib's
`LocalizerMorphism.IsLocalizedEquivalence.of_equivalence` hypotheses.
Its theorem for the commuting quotient square proves that the actual
`localizedSaturationFunctor` is an equivalence.
`localizedSaturationEquivalence` packages it using `asEquivalence`.
Its forward functor is exactly the constructed lift; the inverse,
unit and counit are supplied by Mathlib's equivalence construction.

`localizedSaturationFunctor_spaceFunctor` holds for arbitrary original
index universe `w`. Composing the strict quotient square with the
saturated descended space functor gives the literal original
`spaceFunctor`: use the saturated space recovery equation and the
original saturation-space equality. Strict descent uniqueness then
identifies the composite functor on the entire original quotient with
its own `localizedSpaceFunctor`. This equality covers all quotient
morphisms, including paths and formal inverses.
`localizedSaturationEquivalence_spaceFunctor` specializes it to the
common index universe of the equivalence.

The provenance is internal: actual comparison isomorphisms, full class
preservation and reflection, complete original bounded recovery,
multiplicativity and the two explicit quotient constructions supply the
geometric inputs. Mathlib supplies the categorical localization and
equivalence mechanisms. This compares the specified compatible and
saturated presentation localizations. Identification with the full
intended analytic-space category, calculus of fractions, analytic etale
and quasi-etale sites, equivariant constructions, compact and
distinguished domains, and Harris specializations remain subsequent
obligations.
