# Assignment rebasing from full-datum transport

This is a conditional derived construction. It requires a supplied law that
transports an entire group-valid `KPBuildingDatum` under every isomorphism of
based reductive groups. That law must give group axioms for the target datum,
exact equality of its torus with the prescribed torus, heterogeneous equality
of its inclusion, forward equivariance along the ambient isomorphism, and
geometric compatibility of the inverse building equivalence. This module does
not prove that law and does not prove the unconditional
`ValidAssignmentTorusRebasingStatement`.

`rebaseAssignmentFromDatumTransport` applies the published
`Langlands.GroupScheme.maximalSplitTorusConjugacy` to the original base torus
and the prescribed one. The torus isomorphism is viewed in the commutative
group-scheme category. The supplied transport law then yields full group-valid
data at that torus, equivariant along `Int(g)`. The construction
`KPBuildingDatum.BuildingEquivalence.ofInner` corrects this comparison by source
translation by `g⁻¹`, giving identity equivariance. Finally,
`KPBuildingAssignment.replaceDatum` replaces the complete chosen datum index,
and `replaceDatum_isValid` preserves the full corrected validity, including all
cross-group and field comparisons. The update's exact evaluation lemma gives
both requested torus equalities.

The output is an actual assignment with full validity and the prescribed torus,
conditional on the supplied transport law and original valid assignment. The
construction works in arbitrary universe `u` and introduces no characteristic,
rank, splitness, quasi-splitness or ramification restriction.

The mathematical conjugacy input is Borel–Tits, *Groupes réductifs* (1965),
Théorème 4.21, printed p.93/PDF p.40, through its already-published Library
proof. The remaining steps are internal transport and dependent update.
