# Local compactness through actual affine open charts

This proof establishes the published target
`Langlands.AlgebraicGeometry.PointTopology.SchemePointLocalCompactnessProperty`
through `schemePointLocalCompactness_proof`. It retains commutative rings `R`
and `S` in a common arbitrary universe, `Algebra R S`, and a topology only on
`S`. The value ring is local, a Hausdorff locally compact topological ring,
and satisfies `IsOpenUnits S`. The target scheme is locally of finite type
over `Spec R`; separation, quasi-compactness, finite presentation and global
finite type are not imposed.

Each actual point lifts through an actual affine open chart using localness.
The chart inherits locally finite type over the base. Its actual coordinate
ring is therefore finitely generated, and the existing evaluation-topologized
algebra point space is locally compact by `affineLocalCompactness_proof` from
`AffineProofs`. The published affine point homeomorphism transfers this to
the actual scheme point carrier of that chart.

`isOpenEmbedding_schemeAffineChart` from `SchemeOpenPointProofs` gives an
open embedding from the chart's evaluation-topologized point space into the
exact final topology `schemePointTopology` on the target point carrier. For
any neighborhood at the original point, pull it back into the chart and
choose a compact neighborhood there. Its image is compact by continuity,
is a neighborhood by openness and lies in the original neighborhood. This
constructs exactly the local-compactness class. It asserts no Hausdorffness
of the point space of a nonseparated scheme.

The source of the target is Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Proposition 3.1 and gluing proof,
printed page 4. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The relative formulation is documented by the published target. The
independent publication of the imported open-chart proof is a prerequisite
for submitting this clean proof unit; it is developed in focused child
`aea22f5c-f1ed-4922-8abe-e8bcdd9747f0` of the same parent program.
