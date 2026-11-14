# Restriction of order-linear formal atlas maps

This derived unit restricts actual same-cover formal maps commuting with a
ring action to an actual finer principal cover. It also restricts formal
isomorphisms, preserves identities and composition, and proves the
corresponding square on full compatible families.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
obtained by gluing formal groups over localizations. The constructions here
are derived coordinate infrastructure for that convention. Registered
source: `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
No separate restriction theorem is attributed to the article.

The parameters are commutative rings O and R with an O-algebra structure
on R, a possibly noncommutative O-algebra ring D, and finite coordinate
types in `Type`. The original atlases carry actual `OrderAction D` data
and equal principal covers. A supplied `CoverRefinement` includes a finer
cover with its covering equation, selected original charts, and actual
localization containment witnesses. Tests have the universe v of R;
complete-family modules have universe v + 1. Covers may be infinite.

## Actual formal maps

`OrderAction.Hom.restrict` has underlying map exactly
`BasicAtlas.Hom.restrict`, as `restrict_val` states. Its source action is
`q.orderAction E` and its target action is
`(q.retarget Y h).orderAction E'`. The retargeting carries the selected
original source charts across the equality of covers.

To prove commutation with each element of D, formal-map extensionality
reduces to coordinate series. The finer action coordinates agree with
the directly extended original action coordinates by
`orderChart_coordinates`. The restricted map coordinates agree with the
original map coordinates by `BasicAtlas.Hom.restrict_coordinates`.
The original formal commutation equation then gives the result.

`restrict_id` and `restrict_comp` lift the corresponding equations of
actual underlying formal maps by subtype extensionality. These are
formal-map equations, rather than only equations on evaluated points.

`OrderAction.Iso.restrict` restricts both actual formal inverse maps.
Its two inverse equations follow from preservation of composition and
identity and the original formal inverse equations.

## Full-family realization

`OrderAction.Hom.restrict_onPoints` states that evaluating the restricted
formal map after full-family restriction equals full-family restriction
after evaluating the original formal map. All maps are linear over D.
Its proof is the existing square for the actual underlying formal maps;
the family functions of the order-linear maps are those same functions.

`OrderAction.Iso.restrict_onPoints` expresses the same square using the
constructed linear equivalences whose inverses are actual coefficient
gluing. Naturality of restricted maps and their algebra/Nilp natural
transformations and isomorphisms are provided by the existing
`OrderAction.Hom` and `OrderAction.Iso` constructions.

This unit does not assert comparison of arbitrary different covers,
canonical quotient-class maps, height descent, framing or representability.
