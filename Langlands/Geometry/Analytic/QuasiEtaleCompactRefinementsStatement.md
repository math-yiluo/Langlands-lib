# Legacy finite compact refinements statement — do not use

Author: Worker 21.

> **Do not use `QuasiEtaleCompactRefinementsStatement` as a proof target or
> premise.** The Lean text is retained unchanged for existing consumers.
> Its replacement is `CompactProbeQuasiEtaleCompactRefinementsStatement`,
> on `compactProbeQuasiEtaleTopology` and the same `QuasiEtaleSite X`.
> This correction does not migrate condition (A) or any other consumer.

## What the retained proposition says

`Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleCompactRefinementsStatement K`
quantifies over a complete ultrametric normed field `K` and Hausdorff `X` in
`LocalizedCategory.{u, v, v}`. It asks for
`HasFiniteCompactQuasiEtaleRefinements X`, the old condition (A) in
`Langlands/Sheaf/Equivariant/AnalyticQuasiEtaleRefinements`. This means that
for every object `U` with `IsCompactSpace U.left` (compact and Hausdorff)
and sieve `S ∈ quasiEtaleTopology X U`, there are finitely many arrows
`f i : V i ⟶ U` in `S` with compact Hausdorff sources such that
`Sieve.ofArrows V f ∈ quasiEtaleTopology X U`. Both covering predicates are
for the legacy topology. The proposition is not proved here.

## Why the compactness argument does not apply to this topology

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
§3, printed p. 544 (PDF p. 6), describes covering families by finite unions
of affinoid-domain images that are neighbourhoods of the target points.
Compactness can extract finitely many witnesses when a sieve offers those
neighbourhoods on a compact object. The legacy topology is instead generated
from a precoverage on the whole quasi-étale category. Those neighbourhood
witnesses need not survive pullback through non-Hausdorff objects, so one
cannot begin the argument by assuming a covering sieve contains such a
family.

For the doubled-disc obstruction, glue two copies of a closed disc `B` of
radius two along the complement of their closed unit disc `D`. This is open
gluing as in Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
Publ. Math. IHÉS 78 (1993), Proposition 1.3.3(a), printed p. 24 (PDF p. 21).
The unit disc in the first copy and the whole second copy have affinoid
images whose union is the double, so they pass the old generating-family
test. The old
topology also covers on pullback along the inclusion of the first `B`.
Each arrow of the pulled-back sieve has image in `D` or in `B \ D`. A finite
family of compact Hausdorff sources cannot have dense union of images:
its image is closed in `B`, and exhausting `B \ D` would require that
complement to be a finite union of compact images disjoint from `D` and
hence closed in `B`. The complement is not closed (Gauss points of radii
above one approach the radius-one point). The double maps to the Hausdorff
base `B` by the folding map, so separation of the base is not the remedy.
The formal obstruction uses the two-piece site configuration and a
pointwise lifting or density hypothesis to exclude a finite generating
cover; this Markdown does not claim an unconditional Lean refutation.
See also [the covering-rule warning](QuasiEtaleSite.md).

The compact-probe topology excludes the starting sieve by testing along
that very inclusion of `B`. The new refinement target uses the direct
probe test for both of its covering predicates, rather than assuming finite
refinements for the old generated topology.
