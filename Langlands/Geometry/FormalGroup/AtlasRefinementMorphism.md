# Formal morphisms on finer principal covers

`Hom.restrict` restricts an actual same-cover formal atlas map to a finer
principal cover. `Iso.restrict` restricts its formal inverse as well. The
construction preserves formal identities and composition, and evaluating
the restricted map commutes with restriction of full compatible families.

## Provenance and scope

This is derived infrastructure for Drinfeld's localization-gluing convention:
Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
That paragraph admits formal groups glued from formal groups over
localizations. The restriction and compatibility constructions here are
derived from the implemented chart laws and maps; no separate theorem of
the source is being attributed to this paragraph.

O and R are arbitrary commutative rings with an O-algebra structure on R.
The finite coordinate types in `Type` may differ for the source and target.
Tests are R-algebras in R's universe v; family point modules are in v+1.
Covers may be infinite and the chart laws may vary.

The original atlases have equal covers. The finer cover carries actual
localization containments in selected source charts. Its target refinement
uses the same selected generators. This module does not compare different
choices of source charts, compose successive refinements, prove
transitivity for arbitrary `Comparison` witnesses, or construct a quotient
of presentations, framing, heights, a moduli space or representability.
All maps are actual formal power-series homomorphisms with their formal
O-linearity and compatibility equations; a point equivalence is not input.

## Carrying the refinement to the target

For `q : CoverRefinement X` and `h : X.opens = Y.opens`,
`q.retarget Y h` has q's finer covering set and cover proof. Its source
chart in Y is the same ring element as the selected chart `q.source b` in
X, with membership carried across h. Consequently q's proved localization
unit condition supplies the target's containment condition directly.
Retargeting preserves the selected elements, including after identity,
inverse and composite cover equalities.

## Restricting the formal maps

For `f : Hom X Y h`, the formal map of `f.restrict q` over a finer test is
the composite of three actual formal O-module homomorphisms: q's
identity-coordinate comparison into its selected original X chart,
f's map in that original generator, and the inverse chart comparison into
the restricted Y chart.

`restrict_coordinates` proves that this composite has exactly the formal
coordinate series of f at the selected original chart. Both chart
comparisons have identity coordinate maps, so their composition cancels
using the identity laws for coordinate substitution.

Coefficient naturality follows from f's coefficient-naturality equation
after these coordinate identities. The formal transition square reduces
in the same way: the two refined transition maps have the original
transition coordinates, and f's original formal transition square gives
the required equality.

`restrict_id` proves that the restricted identity is the identity formal
atlas map, using identity coordinate substitution. `restrict_comp` proves
that restriction of a composite equals the composite of the restrictions.
The target refinement of the first map is used for restricting the second
map. The selected source generators agree, and both sides reduce to the
same composite of actual formal coordinate maps.

`restrict_onPoints` evaluates `restrict_coordinates` at the corresponding
component of an arbitrary full compatible family. Extensionality over all
chart tests proves equality of the resulting families. The actual formal
group addition and O-action on these families come from the imported
formal atlas maps; the tuple description does not impose coordinatewise
addition.

## Restricting formal inverses

`Iso.restrict` restricts the forward formal map along q and the inverse map
along `q.retarget Y h`. Retargeting back selects the original generators.
The two formal inverse identities follow from `restrict_comp`, the input
isomorphism's inverse equations, and `restrict_id`. The resulting object
is therefore a genuine formal atlas isomorphism on the finer cover,
before any evaluation on points.
