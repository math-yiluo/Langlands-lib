# Colimits over nonempty finite sets of actual curve places

Author: Worker 208.

`CurvePlaceNonemptyLevelColimitStatement` quantifies over fields `k` and
`F` in a common arbitrary universe, a specified `k`-algebra structure on
`F`, and the existence of an actual `AlgebraicCurve.Place k F`. It uses
the published nonempty finite index, its actual level subrings, and its
canonical cocones. The hypothesis concerns an inhabitant of the concrete
place type; no colimit, support, or topology property is assumed.

Its four conclusions are:

1. Every element of the actual restricted product belongs to a level
   indexed by a finite nonempty set.
2. A map to any topological space in the same universe is continuous
   exactly when its restriction to every such level is continuous.
3. The canonical cocone in `TopCommRingCat` has an `IsColimit` structure.
4. The corresponding cocone in `CommRingCat` has an `IsColimit` structure.

The last two assertions quantify over all cocones in their respective
categories through `IsColimit`, including factorization and uniqueness.
The topology is the existing restricted-product topology on
`CurvePlaceAdeleRing k F`, and each level retains its induced topology.
The arrows and cocone legs are the existing literal inclusions.
The finite index excludes the empty set.

These hypotheses apply to every specified finite extension of
`RatFunc k`, using the constructed `curvePlaceReference k F` and
`curvePlace_nonempty`. That existence construction imposes no perfectness
or separability condition. This application uses the actual curve-place
type; identification with conventional global-function-field places
remains a separate comparison.

The source motivation is the direct-limit assertion in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.1, Section 2 opening. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source uses global fields and finite nonempty sets containing every
archimedean place. This statement is derived ring-level infrastructure:
it uses actual discrete curve places with no archimedean factors, and
states the categorical universal properties together with exhaustion and
final topology. It supplies no proof. Conventional global-place
realization, local compactness, models and geometric point-space
comparisons remain separate obligations.
