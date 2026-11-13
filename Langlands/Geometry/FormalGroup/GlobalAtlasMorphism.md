# Global formal maps and their atlas morphisms

This derived unit constructs morphisms between the atlases induced by global
formal O-module laws. It proves that the singleton atlas comparison recovers
the original formal map on points and is natural in global formal maps.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
glued from formal groups over localizations. The registered original source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The present construction is an internal consequence of the identity-coordinate
comparisons in `GlobalAtlas` and the morphism definition in `AtlasMorphism`.
It is not an additional numbered theorem of the source.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The formal laws have fixed finite coordinate types in `Type`, which can
differ between source and target. The test R-algebras have R's universe v.
The construction restricts each actual global homomorphism to any supplied
common principal-open cover. The comparison with the original point map is
proved for the singleton cover at 1. No comparison for different covers,
refinement invariance, full faithfulness, formal-scheme comparison, moduli
construction or representability is asserted.

## Restriction of the actual formal map

`globalChartHom f a A ha` first takes the source restricted chart to the
directly extended global source using `globalChartIso`. It then applies
the actual coefficient extension of f, and returns to the restricted target
chart with the inverse target comparison. These are formal O-linear maps,
not supplied functions on unrelated carriers.

`globalChartHom_coordinates` proves that the composite's coordinate series
are precisely f's series extended from R to A. Both comparison maps have
identity coordinate maps, so the proof uses the two composition identities.

`ofGlobalHom f s hs` uses these maps to construct an `AtlasMorphism.Hom`
(named `BasicAtlas.Hom` in Lean) between the two `ofGlobalCover` atlases.
For coefficient naturality, composition of coefficient extension identifies
both sides with f's series mapped to the new test algebra, using the
R-algebra map's structural coefficient identity. For transition compatibility,
the transitions have identity coordinates and the coordinate formula makes
both chart maps equal. Formal-map extensionality proves the square.

`ofGlobalHom_id` and `ofGlobalHom_comp` prove that this construction preserves
identity and composition. Equality of the actual formal chart maps reduces
to the identity and composition laws for coefficient extension of coordinate
maps.

## The point comparison

`globalPointEquiv_ofGlobalHom` says that applying the atlas map and then the
singleton linear equivalence agrees with applying f's original map on
nilpotent algebra points after the source equivalence. The proof uses
the component formula for atlas maps and the evaluation formula for the
singleton equivalence, then replaces the restricted map's series by f's
extended series. The resulting expressions are definitionally equal.

`globalPointFunctorIso_natural` packages this same equation at the functor
level. The atlas natural transformation followed by the target comparison
equals the source comparison followed by f's original natural transformation
after `ModuleCat.uliftFunctor`. Extensionality reduces this to the preceding
point equation under `ULift.up`. Thus the universe lift is the one already
required by compatible families, with no additional comparison assumption.
