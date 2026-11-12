# Actual parabolic count for a maximal Levi and the geometric survivor budget

`maximalLeviParabolicCount` proves exactly
`Langlands.GroupScheme.MaximalLeviParabolicCountStatement` over every field.
It is the named entry point for `maximalLeviParabolicCount_core`; the paired
[core proof](MaximalLeviParabolicCountCore.md) describes its full argument and
published prerequisites. No theorem-valued premise is added.

The proof uses `splitComponentStatement`,
`parabolicRootPresentationExistence`,
`MaximalLeviConeComplementLine.range_comp_ne_top_of_not_isIso`,
`ParabolicRootPresentation.restrictedRoots_nonempty`,
`ParabolicRootPresentation.splitComponentEvaluation_pos_of_mem_restrictedRoots`,
`MaximalLeviConeComplementLine.latticePairing_restrict_eq_zero_of_isCentral`,
`maximalLeviConeComplement`, and
`ParabolicRootPresentation.notMem_positiveCone_or_neg_notMem`. Its count maps
the family injectively to `Bool`, according to membership of a fixed nonzero
central-annihilator character in the members' positive cones.

The same unit supplies the numerical application in
[MaximalLeviParabolicBudget](../../Representation/Geometric/MaximalLeviParabolicBudget.md).
For a finite family of pairwise nonconjugate target parabolics whose Levis are
isomorphic to the source maximal Levi, every full-source geometric index
gives a conjugated target parabolic with that fixed embedded Levi. The
published full-intersection results and the supplied geometric intersection
isomorphism give the required actual Levi identification. The lemmas of
[ConjugatedParabolicIndexing](../../Representation/Geometric/ConjugatedParabolicIndexing.md)
use `parabolicSelfNormalizer` to show that these parabolic images distinguish
the actual double-coset indices. The count therefore bounds the sum of all
surviving-index cardinalities by two, retaining every original multiplicity.

Given actual geometric gluings and detection of every irreducible subquotient,
the existing `hasRepresentedJacquetLengthWitness_of_geometricBudget` and
`repLength_le_of_hasRepresentedJacquetLengthWitness` then supply a Jacquet
length witness and a length bound. The first theorem uses the published local
unipotent radical compactness and geometric piece-length proofs; the second
uses exact Jacquet functors and the exact-family length theorem.

This derived route is motivated by Renard V.4.8 (printed p.122 / PDF p.128) and
VI.5.4 (printed pp.173–174 / PDF pp.179–180). It proves the structural count
unconditionally. The geometric-family consequences retain their explicit
family, separation, double-coset, gluing and detection inputs. Thus this unit
does not prove the host task's exact induction-length target. All imported
prerequisites above are proved Library theorems; neither the represented
geometric lemma statement nor VI.5.4 association is assumed or invoked.
