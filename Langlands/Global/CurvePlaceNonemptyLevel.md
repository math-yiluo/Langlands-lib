# Nonempty finite curve-place levels

`CurvePlaceNonemptyLevelIndex k F` is the inclusion-ordered subtype of finite
nonempty sets of the actual `AlgebraicCurve.Place k F`. The fields `k` and `F`
lie in a common arbitrary universe and have a specified `k`-algebra structure.
The index type excludes the empty finite set literally.

`curvePlaceNonemptyLevelForget` forgets the nonemptiness proof.
For any supplied actual place `p`, `curvePlaceNonemptyLevelEnlarge k F p`
is the monotone map taking `S` to `insert p S`. Its value contains `S`;
the cofinality lemma states explicitly that every finite set is contained
in a nonempty finite one. Union constructs a common upper bound within this
index type and proves directedness. If the place type is empty, the index
type is empty too; the enlargement construction requires an actual place.

`curvePlaceNonemptyAdeleLevelDiagram` sends a nonempty finite set `S` to
the published actual level subring `curvePlaceAdeleLevel k F S.val`, with
its existing induced topology. An arrow is the literal ring inclusion.
These maps are continuous because composition with the ambient subtype
inclusion is the source subtype inclusion.
`curvePlaceNonemptyAdeleLevelCocone` has the actual restricted product
`CurvePlaceAdeleRing k F` as vertex and the literal continuous inclusions as
legs. The ring diagram and cocone forget topology through the standard
functor to `CommRingCat`.

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed p.1, Section 2
opening. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source requires finite nonempty sets containing all archimedean places.
For the curve-place setting there are no archimedean factors in this
construction. An actual function-field application must supply a place
and establish the conventional global-place comparison separately.
The present contribution constructs the literal diagram and cocone;
their colimit universal properties and the geometric point comparisons
are separate assertions.
