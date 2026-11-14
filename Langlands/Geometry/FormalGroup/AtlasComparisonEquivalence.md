# Equivalence laws for formal atlas comparisons

`Comparison.refl`, `Comparison.symm` and `Comparison.trans` construct
reflexive, symmetric and transitive comparisons of formal module atlases.
Each comparison contains two actual principal-cover refinements and an actual
formal atlas isomorphism on their common finer cover. The induced O-linear
equivalences on full compatible point families realize identity, inverse and
composition.

## Provenance and scope

This is derived infrastructure for Drinfeld's convention allowing formal groups
obtained by gluing formal groups over localizations: Drinfeld, *Coverings of
p-adic symmetric regions* (1976), printed p.109, paragraph immediately before
section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The particular comparison constructions and evaluation identities are derived
from the implemented localization refinements, formal maps and full-family
descent. They are not attributed as separately stated theorems of Drinfeld.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The atlases may have different finite coordinate types, all in `Type`.
Their principal covering sets may be infinite, and their chart laws may vary.
Tests are R-algebras in R's universe v; the full-family point modules lie in
v+1. Comparisons require genuine formal isomorphisms after refinement, rather
than arbitrary isomorphisms of point functors.

This module does not identify comparison witnesses, prove strict identity or
associativity equations between witnesses, or construct a quotient of atlas
presentations. It does not assert that arbitrary comparisons of the same
atlases induce the same point map. It does not construct framing, heights,
moduli or representing objects.

## Constructing the formal comparisons

`refl` uses the actual reflexive refinement twice and the identity formal
isomorphism. `symm` exchanges the two refinements and reverses the formal
isomorphism.

For a comparison f and a further refinement q of its left finer atlas,
`refine` composes the left containment with q. It retargets q to the right
finer atlas, whose cover is equal, and composes that containment as well.
The new formal isomorphism follows three actual maps: the comparison between
direct and successive restriction on the left, the restriction of f's formal
isomorphism, and the inverse direct-versus-successive comparison on the right.
Thus changing covers also constructs the required formal coordinate maps.

`join f g h` applies when f's right finer cover and g's left finer cover
are equal. Both middle refinements are refinements of the same original
atlas Y. The proved `sourceIso` compares their possibly different selections
of original Y-charts. Composing f's formal isomorphism, this source-change
isomorphism and g's formal isomorphism gives the joined comparison.

`trans f g` makes this construction applicable to arbitrary comparisons
X to Y and Y to Z. The imported `commonLeft` and `commonRight` refine
f's left finer atlas and g's left finer atlas to the actual cover of
products of their generators. After applying `refine` to each comparison,
the two middle covers are this same product set. `join` then constructs
the composite. The construction uses the proved unit-ideal cover and
localization containments of the product refinements.

## Realizing the operations on full families

`onPoints_restrict` characterizes a comparison's point map: restricting its
output to the right finer atlas equals applying its formal coordinate map
to the restriction of its input to the left finer atlas. This is the
right inverse equation of the proved right restriction equivalence.

`onPoints_refl` uses injectivity of that restriction equivalence and
evaluation of the identity formal map. `onPoints_symm` identifies the
reversed comparison's O-linear equivalence with the inverse equivalence.

`onPoints_refine` proves that further refinement preserves the map on original
full families. After applying injectivity of the final restriction equivalence,
evaluation of formal composites is expanded by `Hom.onPoints_comp`.
The direct-versus-successive restriction squares on the left and right,
the restricted formal-map square and `onPoints_restrict` identify the two
routes. The inverse right comparison is handled by its linear equivalence
inverse law.

`onPoints_join` again uses injectivity of the last restriction equivalence
and evaluation of the actual formal composite. The source-change square
identifies the two middle restrictions of the same Y-family, while
`onPoints_restrict` for f and g supplies the outside squares.
Finally `onPoints_trans` combines `onPoints_join` with the two
`onPoints_refine` equations. It states
`(f.trans g).onPoints A x = g.onPoints A (f.onPoints A x)`
for every R-algebra A and every full compatible X-family x.
All maps carry the actual formal-law addition and O-action from the imported
formal maps and restriction equivalences.
