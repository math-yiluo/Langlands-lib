# Smooth algebraic-space maps on points over complete normed fields

Author: Worker 109.

This module states a local prerequisite for the proof of Conrad's Theorem
5.9. It contains no proof.

`CompleteFieldSmoothSpacePointOpenStatement` says that over any complete
nontrivially normed field `K`, a smooth morphism `f : X → Y` of separated
algebraic spaces locally of finite type over `Spec K` induces an open map
on their actual `K`-valued points. The source and target carry the published
`etaleChartTopology`.

The algebraic spaces, morphisms, `RingPoints` and topologies are the actual
published objects. `IsSeparated` means that the diagonal is a representable
closed immersion. `LocallyOfFiniteTypeOverBase` means that the space has an
étale surjective atlas whose structure morphism to the base is locally of
finite type. `IsSmoothMorphism f` means that there are schemes `U`, `V`,
an étale surjective map `U → X`, an étale map `V → Y`, and a smooth scheme
map `U → V` making the square commute. It does not require `f` to be
representable.

The field may have either characteristic and either an archimedean or
nonarchimedean norm. The spaces need not be quasi-compact. The statement
does not impose surjectivity or geometrically connected fibres; those
conditions enter the subsequent adelic argument through its arithmetic
part. There is no assumed Lang–Weil estimate or unproved local-openness
input in the statement.

The provenance is derived from Brian Conrad, *Weil and Grothendieck
approaches to adelic points*, 31 December 2011, printed p.11 (local smooth
openness for schemes), p.15 (the étale-chart topology and rational-point
lifting through étale scheme charts), and p.17 (the proof of Theorem 5.9
carries the scheme argument over to spaces). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad does not state this exact local algebraic-space assertion as a
separately numbered theorem. It isolates the local step needed before the
adelic product argument. Separatedness keeps the spaces within the
corrected scope of the published topology package.

The scheme counterpart is already proved as
`Langlands.AlgebraicGeometry.PointTopology.completeFieldSmoothPointOpen`
in `CompleteFieldSmoothOpenProof`. Other available inputs are
`RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement`,
`isOpenMap_schemePointsMap`, and smoothness descent along surjective étale
scheme maps (`Langlands.AlgebraicGeometry.smoothEtaleSourceDescent`).
To prove this new statement one still has to implement the passage from
the defining smooth chart square to compatible rational-point charts and
then descend openness through their continuous surjective point maps.
These are remaining proof obligations, not fields of assumed data.
