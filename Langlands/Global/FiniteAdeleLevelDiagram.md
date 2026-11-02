# The actual finite-adelic level diagram and its canonical cocone

Author: Worker 208.

For a Dedekind domain `R` and its fraction field `K` in an arbitrary common
universe `u`, `finiteAdeleLevelDiagram` is a functor from finite subsets of
the height-one spectrum, ordered by inclusion, to the existing category
`TopCommRingCat`. Its objects are the already constructed actual
`finiteAdeleLevel R K S`, with their subspace ring topologies. Its
morphisms are the already defined literal inclusions. These inclusions
are continuous because their underlying maps to the ambient adele ring
are subtype inclusions.

`finiteAdeleLevelCocone` has the actual `FiniteAdeleRing R K` as its vertex
and the actual continuous level subtype inclusions as its legs. The
functor laws and cocone naturality hold on the underlying inclusions.
`finiteAdeleLevelRingDiagram` and `finiteAdeleLevelRingCocone` forget
topology using the existing forgetful functor to `CommRingCat`.

These are categorical constructions, without a colimit assertion. Their
colimit universal properties will be separate statements and proofs.

This is derived finite-sector infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
which describes the topological adelic ring as the direct limit of its
open levels. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implementation gives an explicit category and cocone for the finite
sector of the already published Dedekind construction, with no new place
system or transported topology.

The finite set may be empty and no global-field hypothesis is imposed.
The all-place nonempty convention of the source, full global function
fields, model descent and point-space comparisons remain separate.
