# Restricted products over actual discrete curve places

Author: Worker 208.

For fields `k` and `F` with an algebra structure `k → F`, the existing
`AlgebraicCurve.Place k F` is a concrete nontrivial principal valuation
subring of `F` containing the image of `k`. Its published DVR instance
and maximal height-one prime give an actual adic completion of `F` and
an actual completed valuation ring. `curvePlaceCompletion` and
`curvePlaceCompletionIntegers` name those existing objects.

`CurvePlaceAdeleRing k F` is Mathlib's cofinite restricted product of
these completed fields relative to their completed valuation rings.
Its ring structure and restricted-product topology are inherited from
Mathlib. Openness of the completed valuation rings proves that it is a
topological ring. No abstract system of places or assumed adelic
comparison is introduced.

For a finite set `S` of these actual places, `curvePlaceAdeleLevel` is
the subring integral at every place outside `S`, with the ambient
subspace topology. It is open, and enlarging `S` gives literal subring
inclusions. `curvePlaceSIntegers` is the subring of `F` lying in every
place's valuation subring outside `S`. Constants give its canonical
`k`-algebra structure, compatible with its inclusion in `F`.

The completion map sends every element of a place's valuation subring
into the completed valuation ring. Applying this fact away from `S`
constructs `curvePlaceAdeleLevelDiagonal`, a ring map from the actual
outside-`S` integers to the level ring. The corresponding algebra
structure is induced by this map. Its coordinate formula is exactly
the actual field-to-completion map; this construction needs no assumed
finite-pole theorem for arbitrary elements of `F`.

`curvePlaceAdeleLevelProductEquiv` is an explicit ring equivalence
between the level and the product of completion fields in `S` and
completed valuation rings outside `S`. Its inverse assembles the
given coordinates; integrality outside a finite set puts the result
in the restricted product. The two final lemmas give both coordinate
formulas. This unit claims a ring equivalence, without a product
homeomorphism or a categorical colimit assertion.

The provenance is derived infrastructure for Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011
(registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).
The open adelic levels on printed p.1 and completed local factors on
printed pp.6–8 motivate this construction. The actual place and
completion constructions are reused from the published Library and
pinned Mathlib; the ring-level construction follows their canonical
maps.

The field extension need not be a global function field for these
definitions. An empty finite `S` is allowed at this construction
stage. Conrad's nonempty all-place convention, identification of these
places with all conventional places of a global function field,
finite-pole support for every element of that field, the full-field
diagonal, presentation independence, and the geometric point-space
and whole-paper results remain separate obligations. No assertion in
this unit assumes or discharges those comparisons.
