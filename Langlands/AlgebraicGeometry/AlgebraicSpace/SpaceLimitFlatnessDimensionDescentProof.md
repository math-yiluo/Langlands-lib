# Proof of Theorem 3.4(2) for spaces: flatness and fibral pure dimension

Authors: Worker 156 and Worker 3519.

`spaceLimitFlatnessDimensionDescent` proves the unchanged published statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitFlatnessDimensionDescentStatement`.
It retains arbitrary cofiltered limits of affine schemes, a specified stage,
and quasi-separated source and target algebraic spaces over that stage with
quasi-compact, locally finitely presented étale surjective atlases. The conclusion
is descent of `IsFlatMorphism` and, for every natural number `d`, descent of
`HasGeometricallyConnectedFibres` together with `HasPureFibreDimension d`, with
their published definitions. Geometric connectedness includes nonemptiness.
No hypothesis is added.

The statement formalizes Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), Theorem 3.4(2), printed p.5, extended to
algebraic spaces on printed p.13. The source is registered as
`conrad-2011-weil-grothendieck-adelic-points`, PDF SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The implemented Lean proof applies the published theorem
`spaceLimitFlatnessDimensionReduction` to the published theorem
`spaceLimitGeometricallyConnectedFibresDescent`. The latter proves exactly
`SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f)`,
which is the reduction's only premise. The resulting term has exactly the
original statement as its type.

The reduction supplies flatness descent directly. For the other conjunct it
first descends pure fibre dimension to an incoming stage, then descends
geometric connectedness from that stage to a further incoming stage. Base-change
preservation of pure dimension and the comparison of iterated and direct base
change place both properties at the same composite incoming stage. The reverse
implication applies each descent equivalence to the common stage witness.
The connected-fibre theorem detects the constructible count-one locus on
the actual target-chart limit over the incoming slice category.

This file is an internal composition of those two Library results. Its proof
contains no additional geometric argument or conditional premise. Worker 3519
provided the composition draft; Worker 156 verified its published inputs and
prepared the proof submission.
