# Localization of saturated strong atlas maps

This is an internal application of Mathlib's constructed categorical
localization to `SaturatedAtlasPresentation` and its full
`quasiIsomorphisms` property. The coefficient field is a complete
ultrametric normed field. Objects are actual affinoid atlas presentations
containing all local full domains, and original arrows retain the entire
`StrongHom` family of bounded algebra pullbacks at admissible chart pairs.
The inverted arrows have both an ambient homeomorphism and full
affinoid-domain representations at every such pair.

`LocalizedCategory` uses Mathlib's path category with original arrows and
formal inverses, quotiented by the identity, composition and two inverse
relations. It constructs a category from these particular original maps
and relations. `localizationFunctor` is its quotient functor and has
Mathlib's `IsLocalization` property. `localizedObjectEquiv` identifies its
objects with the original saturated presentations. Morphism universes
are those of Mathlib's standard localization, the maximum of the original
object and morphism universes; no smaller universe is asserted.

`localizedQuasiIso` gives the actual isomorphism for each original full
quasi-isomorphism. Its forward arrow is the quotient image of that map;
the two proved equations identify its formal inverse as a two-sided
inverse in the quotient. This makes no claim that it has an inverse in
the original category.

`descend` constructs the extension of any functor sending these
quasi-isomorphisms to isomorphisms, using Mathlib's quotient lift. The
factorization through `localizationFunctor` is equality of functors, and
`descend_unique` proves uniqueness among strict factorizations using
Mathlib's uniqueness theorem. `localizedFunctorEquivalence` also supplies
the equivalence of functor categories, including their natural
transformations, with the full category of functors inverting precisely
the specified morphism property.

`spaceFunctor_inverts_quasiIsomorphisms` proves the required inversion
premise for the original literal-space functor: the homeomorphism clause
of `IsQuasiIso` gives an isomorphism of topological spaces by Mathlib's
`TopCat.isIso_iff_isHomeomorph`. Thus `localizedSpaceFunctor` is actually
constructed by descent. Its composite with the quotient functor is the
original space functor. `localizedSpaceComparison` records the resulting
natural isomorphism, whose component at each original presentation is
the identity of its literal ambient space. The object and map equations
recover exactly that ambient space and original continuous map.

For the formal inverse of any original quasi-isomorphism,
`localizedSpaceFunctor_map_quasiIso_inv` proves that the descended
continuous map is the inverse of its original ambient homeomorphism.
The proof identifies the image isomorphism by its forward arrow and
then takes equality of inverses. `localizedSpaceFunctor_unique` proves
uniqueness of this space functor among strict extensions.

The provenance is entirely internal: the actual saturated category,
full quasi-isomorphism property, original homeomorphism condition, and
Mathlib's localization construction and universal property supply the
inputs. This unit does not identify this localization with the full
category of analytic spaces or prove extension from arbitrary original
atlases. Those comparisons, and the analytic and equivariant site
constructions, remain separate obligations.
