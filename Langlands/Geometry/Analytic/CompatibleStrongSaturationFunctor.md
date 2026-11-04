# The actual saturation functor on original compatible atlas maps

This is an internal categorical consequence of the actual full-domain
enlargement, compatible strong-map composition and unique bounded extension
already constructed in the imported modules. It uses the explicit original
local compatibility convention of `CompatibleStrongMaps`. Its extension
recovers every original admissible bounded map, with heterogeneous equality
accounting only for the chosen original-chart algebra identifications.
No further interpretation of the external compatibility convention is needed
for the results here.

`StrongHom.ext_on_original` determines a strong map between the two
constructed enlarged atlases by its continuous map and one complete bounded
pullback per original source parent, to an original target. Each enlarged
source chart lies in its representative's original parent. The restriction
equation from the parent determines its map to the chosen original target.
Saturated-source extensionality then determines the pullbacks to every other
admissible enlarged target. Thus equality uses complete bounded maps rather
than their actions on spectrum points.

`CompatibleStrongHom.saturationExtension_id` computes the extension on the
original diagonal chart pairs. Original recovery and the original restriction
identity identify its bounded map with the bounded identity. The enlarged
identity has that same bounded map, after the proved identification of the
original chart's chosen algebra. Extensionality gives the whole identity.

`saturationExtension_comp` chooses an admissible original source,
intermediate and final chart chain. Recovery for the saturated composite
identifies its bounded map with the composite of the two extended bounded
maps. Recovery for each extension identifies this complete composite with
the original bounded composite. Recovery for the original compatible
composite gives the same result. A transport lemma eliminates the three
proved algebra equalities and combines the heterogeneous map equalities;
this is transport of actual bounded maps. `ext_on_original` then proves
equality on all enlarged charts. The argument imposes image containment
only along the chosen chain and makes no additional containment assumption
about an unrelated target.

`saturationExtension_injective` recovers equality of original compatible
maps from equality of their extensions. Their continuous maps agree, and
original bounded recovery identifies their pullbacks at one admissible
target per original source. Original coherent extensionality identifies
the entire original map families.

`CompatibleAtlasPresentation.saturationFunctor` sends an actual
presentation to `SaturatedAtlasPresentation.ofSaturation`, on the literal
original ambient space, and sends a morphism to its constructed
`saturationExtension`. The identity and composition equations are the
complete-map equalities just proved. It is faithful by original recovery.
Its composite with the existing saturated `spaceFunctor` is literally the
original compatible `spaceFunctor`.

The base is a complete ultrametric normed field, with no nontrivial-valuation
assumption. Original presentations have universes `u`, `v`, `w`; both
enlarged index types lie in `v`, so the functor has target
`SaturatedAtlasPresentation.{u,v,v}` and needs no reindexing. No directed
chart family, greatest chart, assumed extension output or assumed functor
law is used. Fullness of this functor, categorical equivalences, analytic
localization comparisons, etale sites and equivariant constructions remain
subsequent work.
