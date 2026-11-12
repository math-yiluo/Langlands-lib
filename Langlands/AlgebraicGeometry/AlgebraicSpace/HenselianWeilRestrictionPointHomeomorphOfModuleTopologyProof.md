# Corrected finite Weil restriction point homeomorphism

Author: Worker 172.

`Langlands.AlgebraicGeometry.AlgebraicSpace.henselianWeilRestrictionPointHomeomorphOfModuleTopology`
proves exactly the published proposition
[`HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement`](HenselianWeilRestrictionPointHomeomorphOfModuleTopologyStatement.md).
For a finite extension `K → K'` of henselian nontrivially normed fields with
`NormedAlgebra K K'` and `IsModuleTopology K K'`, and every quasi-separated
finite-type algebraic space `Y'` over `Spec K'`, it supplies an algebraic-space
structure on the actual Weil restriction sheaf and proves that its canonical
base-point equivalence is a homeomorphism for the independently defined
étale-chart topologies.

The theorem retains the full universe parameter, arbitrary finite extensions,
archimedean and nonarchimedean fields, and incomplete fields satisfying the
module-topology hypothesis. Representability and the required geometry of the
restriction are established in the proof. No additional geometric or field
hypothesis is imposed.

## Implemented proof

Finite dimensionality over a field supplies the finite-module instance, and
modules over a field are projective. Apply the published
`spaceWeilRestriction`, from
[`SpaceWeilRestrictionProof`](SpaceWeilRestrictionProof.md), to `Y'`.
This is Conrad's Lemma 5.10: it produces the algebraic-space witness `h` for
`(ringWeilRestriction K K').obj Y'.toSheaf`, quasi-separatedness and finite type
of `ringWeilRestrictionSpace K K' Y' h`. Its additional conditional
separatedness and finite-presentation conclusions are unused here.

The private helper `finiteTypeAtlasLocallyFiniteType` retains the same
surjective étale scheme atlas from `FiniteTypeOverRing`, keeping local finite
type of the structure map and forgetting only its quasi-compactness. Apply it
to the input and the restriction. Combining each result with the corresponding
quasi-separatedness proof gives the two
`IsQuasiSeparatedLocallyFiniteType` hypotheses of the published theorem
`isHomeomorph_ringWeilRestrictionBasePointsEquiv`, from
[`WeilRestrictionPointComparison`](WeilRestrictionPointComparison.md).
That theorem, applied with both henselian predicates and the explicit module
topology, proves the required homeomorphism for this same witness `h`.

The imported comparison proves forward continuity by scheme-map adjunction and
continuous change of coefficients. It proves inverse continuity using open
affine étale chart point maps and the affine Weil restriction homeomorphism.
The latter uses the module topology on `K'`. The underlying map remains
`ringWeilRestrictionBasePointsEquiv`; the two topologies are the independently
defined `etaleChartTopology` instances in the target statement.

## Provenance

This is a derived assembly of the published geometric theorem and point
comparison. Its source motivation is Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Lemma 5.10 and Proposition
5.11(1), printed pp.17–18, with the module-topology hypothesis from Example 2.4,
printed p.3. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paired statement explains the correction of the literal proposition and
the incomplete-henselian inseparable obstruction. This proof targets that
corrected declaration and leaves the original statement pair unchanged.
