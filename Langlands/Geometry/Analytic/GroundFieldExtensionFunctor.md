# The ground field extension functor on compatible and saturated atlases

`AffinoidAtlasPresentation.GroundFieldExtension.compatibleFunctor K L`
sends each atlas presentation over `K` to its quotient ground field
extension over `L` and each `CompatibleStrongHom` to `compatibleMap K L f`.
It applies to arbitrary complete ultrametric normed fields with
`NormedAlgebra K L`.

`pointMap_id` computes the point map of the identity on each extended
source chart using scalar extension of the identity bounded homomorphism.
`pointMap_comp` chooses an intermediate chart containing the image of
each source chart, then a final chart containing the image of the
intermediate one. The bounded pullback of the composite on this chain is
the composite of the bounded pullbacks, and scalar extension preserves
that equation. Computing on the quotient chart representatives proves
the equality of continuous maps. `compatibleMap_id` and
`compatibleMap_comp` prove equality of the full compatible strong maps
using extensionality from the continuous map and one admissible
pullback per source chart.

`saturatedLocalizedFunctor K L` starts with
`SaturatedAtlasPresentation K`. Its inclusion into the compatible
category equips every original `StrongHom` with the compatibility
supplied by source saturation. The functor then applies
`compatibleFunctor K L`, saturates the extended presentations and maps
over `L`, and applies the localization functor to
`SaturatedAtlasPresentation.LocalizedCategory` over `L`.
The object after saturation uses the space of the extended quotient
presentation.

This is a derived implementation of Berkovich's ground field extension
in §1.4, printed p. 30 (PDF p. 27), using compatible strong morphisms
and saturation as in Definition 1.2.7 and Proposition 1.2.8, printed
p. 18 (PDF p. 15). The registered source is
`berkovich-1993-etale-cohomology`, Vladimir G. Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993).
[Chart maps and the weak-map counterexample](GroundFieldExtensionMaps.md)

Descent through quasi-isomorphisms to the localized source category
over `K`, towers of field extensions, fiber products, and the comparison
`(X^an)_L = (X_L)^an` are not treated in this module; towers of field
extensions are treated in `GroundFieldExtensionTowerNaturality`.
