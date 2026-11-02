# Actual full number-field adelic level diagrams and cocones

Author: Worker 208.

For any number field `K` in an arbitrary universe `u`,
`numberFieldAdeleLevelDiagram K` is the functor from finite sets of actual
finite places, ordered by inclusion, to `TopCommRingCat`. Each object is
the existing full level subring of `Adeles K` with its induced topology;
each arrow is the literal inclusion of levels and is continuous for those
topologies. `numberFieldAdeleLevelCocone K` has the existing full adele ring
as vertex and the actual continuous subring inclusions as legs.

The finite-place set `S` corresponds to the existing nonempty all-place set
`numberFieldLevelPlaces K S`, which includes every archimedean place.
In particular the empty finite-place set retains all infinite factors.
No archimedean coordinate is restricted by the level condition.

`numberFieldAdeleLevelRingDiagram` and `numberFieldAdeleLevelRingCocone`
are their images under the forgetful functor to `CommRingCat`. This
construction asserts no colimit universal property; that is a separate
statement and proof.

This is derived categorical infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
which describes the topological adelic ring as the direct limit of open
level subrings. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implementation reuses the actual full number-field level construction
and mirrors the finite-sector diagram. Function-field all-place
realization, model descent, scheme-point and algebraic-space comparisons
retain their separate obligations.
