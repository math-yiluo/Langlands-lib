# Same-compact Cartan transport and chamber equivalence under global validity

This internal derived unit constructs
`validSpecialCompactStandardLeviChamberEquiv` at arbitrary universe `u` and
proves the ambient and same-compact standard-Levi Cartan comparisons used in
that construction. Its field is any nonarchimedean local field, and its group
is any connected reductive group scheme over that field. The hypothesis is a
supplied globally valid corrected KP assignment. No such assignment is
constructed. Global validity is stronger than single-group local availability,
so this does not prove `AvailableRenardCartanStatement` or the unconditional
joint existence target of Task 4169.

`specialCompactCartanComparison_changeCentralizer` transports a supplied
special-compact Cartan comparison between two actual representatives of the
same torus centralizer. It uses the canonical represented-centralizer
isomorphism, its published point-map and translation identities, identity
transport on the real cocharacter space, and preservation and reflection of
the rational-character norm kernel. The proof maps dominant representatives
through that isomorphism for coverage and pulls both representatives back
through its bijection on rational points for classification. Equality of
translations gives equality of positive centralizer valuations, hence
equivalence of the dominance conditions.

`specialCompactCartanComparison_on_subgroup_of_heq` removes an equality of
source tori and a heterogeneous equality of their inclusions. It then applies
the preceding transport at the prescribed subgroup, using its equality with
the supplied apartment's special compact subgroup.

`validSameCompactLeviCartanComparison` applies to every generic cocharacter,
every special vertex of the original apartment, and every subset of its
simple relative roots. For the associated actual standard Levi, published
`availableSpecialLeviCompact` supplies locally available Levi data,
the prescribed torus, and a special vertex whose special compact subgroup is
exactly the original ambient compact's Levi preimage. The available ambient
Cartan comparison applies to this Levi datum. The preceding transport puts it
on the original centralizer through `standardLeviCentralizerDatum`, retaining
the original torus map and restriction-evaluation bijection. This proves
coverage and norm-kernel classification for the same compact Levi
intersection, using the canonical factor of the original centralizer.

`validSpecialCompactStandardLeviChamberEquiv` applies the existing
`sameCompactLeviChamberEquiv` to this proved comparison. Its domain is the image
of the original centralizer valuation cut by the Levi dominant chamber. Its
codomain is the double-coset quotient of the actual standard Levi's rational
points by the preimage of the original compact subgroup. The torus map into
the centralizer and the restriction-evaluation bijection are unchanged.
Coverage and classification are derived from validity rather than assumed as
additional inputs.

`validSpecialCompactRenardCartanComparison` uses the published ambient
comparison for the original assignment and the preceding same-compact
comparison for each standard Levi. Published algebraic factorization, root
containment and lattice comparison supply the remaining compatibility clauses.

The provenance is internal composition of the published results in
`CrossTorusCentralizerCompatibility`, `CrossTorusComposition`,
`ValuationBuildingIsoTransport`, `AvailableSpecialLeviCompactProof`,
`AvailableRenardAmbientComparison`, `RenardLeviCentralizerCompatibility`,
`RenardCartanAlgebraicComparison` and `JointBasisReductionProof`. The
mathematical source and scope of their inputs remain described by those
published Lean/Markdown pairs. This module supplies neither building
availability nor the simultaneous basis, and does not prove the unconditional
joint existence target.
