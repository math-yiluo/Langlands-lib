# Reduction of finite-field solvability to three structural inputs

This is a derived assembly of the existing group-scheme interfaces. It retains
`RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`,
`ParabolicDynamicStatement`, and `FiniteFieldQuasiSplitStatement` as explicit
premises. It does not prove the unconditional
`FiniteFieldCentralCocharacterSolvableStatement`.

`CentralCocharacterReductiveQuotientData G` records an actual ground-field
unipotent radical, its inclusion into `G`, an actual represented fppf quotient,
connected reductivity of that quotient, and centrality of every cocharacter of
the quotient over the original field. The data include the full all-test kernel
identity in `RelativeRoot.IsFppfQuotient`; they do not assert surjectivity of
the quotient map on every original test scheme.

Over a perfect field, `nonempty_centralCocharacterReductiveQuotientData` first
uses `unipotentRadicalExistence` and `unipotentRadicalQuotient`. The theorem
`perfectFieldPseudoReductive` makes the quotient connected reductive.
The radical is smooth, connected, affine, and unipotent. Therefore
`exists_cocharacter_lift_of_perfectField_unipotent_kernel` lifts every actual
cocharacter through the quotient, subject to the retained stable-vector premise.
Affineness of the source and quotient makes the quotient map quasi-compact;
its fppf quotient structure supplies flatness and scheme surjectivity.
`Dynamic.central_cocharacters_of_fpqc_of_lifts` then descends centrality to every
ground-field cocharacter of the quotient. The construction
`centralCocharacterReductiveQuotient` chooses one such package using classical
choice.

For any such package with a quasi-split quotient,
`CentralCocharacterReductiveQuotientData.isSolvableGroupScheme` applies
`IsQuasiSplit.isSolvableGroupScheme_of_central_cocharacters`. That result uses
the retained dynamic comparison to make a solvable Borel inclusion an
isomorphism. Then
`isSolvableGroupScheme_of_unipotent_fppfQuotient` carries solvability across
the radical.

Finally, `finiteFieldCentralCocharacterSolvable_of` uses that a finite field
is perfect and applies the retained finite-field quasi-splitness premise to the
constructed reductive quotient. The resulting implication has precisely the
existing finite-field target as its conclusion, for arbitrary universe `u`.
Its cocharacters remain over the original finite field, and its solvability
conclusion is the existing geometric `IsSolvableGroupScheme` predicate.

The proof imports the radical existence and quotient proofs and the perfect-field
comparison from `Reductive`, the homomorphism lift from
`Rational.SplitUnipotentQuotientHomLift`, centrality descent from
`Dynamic.CentralQuotient`, the quasi-split reduction from
`Rational.CentralCocharacterReduction`, and solvability of extensions from
`Absolute.SolvableQuotientExtension`. No new literature assertion is introduced;
the three named structural propositions remain obligations.
