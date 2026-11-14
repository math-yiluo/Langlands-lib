# Formal comparison of source-chart selections

`CoverRefinement.sourceIso` constructs an actual formal atlas isomorphism
between two refinements of the same original atlas with equal finer covers.
The refinements may select different original charts. The comparison uses the
original transition between those selected charts, and commutes with restriction
of every full compatible original family.

## Provenance and scope

This is derived infrastructure for Drinfeld's localization-gluing convention:
Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The paragraph allows formal groups obtained by gluing formal groups over
localizations. The comparison here is derived from the implemented original
chart transitions and their laws; it is not attributed as a separate source
theorem.

O and R are arbitrary commutative rings with an O-algebra structure on R. The
single coordinate type is finite and lies in `Type`. Tests are R-algebras in
R's universe v, and family point modules lie in v+1. The possibly infinite
principal covers support varying formal laws. Both refinements belong to the
same original atlas, and equality of their finer covering sets is input.
Their source choices need not agree. All formal homomorphisms and inverse
equations are constructed. No point equivalence is input.

This module does not establish transitivity of arbitrary different-atlas
`Comparison` witnesses or construct the quotient of atlas presentations.
It does not construct framing, heights, moduli, or representing objects.

## Comparing the selected original laws

For refinements q and r and `h : q.opens = r.opens`, the generator b on r's
cover is the same ring element as `sourceChart h b` on q's cover. Both selected
original charts are defined over every test in that finer principal open,
by the proved localization containment conditions.

`sourceChartIso` first compares q's finer law with its selected original law,
then uses X's actual transition to r's selected original law, then uses the
inverse chart comparison into r's finer law. `sourceChartIso_coordinates`
proves that its coordinate map is exactly that original transition, since
the two chart identifications have identity coordinate series.

## Assembling actual formal atlas maps

`sourceHom` uses these chart maps. Naturality follows from the original
transition's coefficient naturality. The transition square compares two routes
from q's selected source for b to r's selected source for c. The cocycle law
identifies both routes with the direct original transition. Identity-coordinate
substitutions account for the finer chart comparisons on both sides.
`sourceHom_coordinates` records the resulting original transition coordinates
for the actual atlas map.

`sourceHom_id` compares one selection with itself. The original transition's
self law identifies its coordinates with the formal identity, and formal
homomorphism extensionality gives equality of atlas maps.

`sourceHom_comp` proves that changing the selection from q to r and then from
r to s equals the direct change from q to s, with the corresponding composite
cover equality. After removing the identity chart comparisons, this is exactly
the original transition cocycle law. These are equalities of actual formal
maps before evaluation on points.

`sourceIso` uses `q.sourceHom r h` and `r.sourceHom q h.symm`. Both formal inverse
equations follow from `sourceHom_comp` and `sourceHom_id`.

## Compatibility on full point families

`source_onPoints` states that applying the constructed formal comparison to
q's restriction of x equals r's restriction of x, for every R-algebra A and
every full compatible X-family x over A. Family extensionality reduces the
claim to every arbitrary chart test and structure map from A. The coordinate
identity above turns the evaluated formal comparison into the original
transition. The transition-compatibility equation of x identifies the two
selected original components. O-linearity comes from the actual formal
homomorphisms and the imported restriction maps, with the formal group laws
on the point modules.
