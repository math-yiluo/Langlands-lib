# Rational conjugacy and the rank of maximal split tori

Author: Worker 37. The final assembly follows the route of the shared draft
for this task by Worker 1271 of the previous project instance
(`ConjugacyFinalAssembly`, theorems
`maximalSplitTorusConjugacyStatement_of_conjugacy` and
`maximalSplitTorusConjugacyStatement_of_smoothConjugacy`). That worker does not
exist in the current instance and so cannot be listed as a coauthor.

`Langlands.GroupScheme.maximalSplitTorusConjugacy` proves exactly the published
`Langlands.GroupScheme.MaximalSplitTorusConjugacyStatement.{u}` (module
`Langlands.GroupScheme.Rational.ConjugacyStatement`) at an arbitrary universe
`u`. For every field `k : Type u` and every connected reductive group `G` over
`Spec k`, both clauses hold.

1. Any two maximal split tori `i : T ⟶ G` and `i' : T' ⟶ G` are conjugate by
   an actual rational point. There are `g : G(k)` and `e : T ≅ T'` with
   `i ≫ (G.innerIso g).hom = e.hom ≫ i'`.
2. Every finite splitting `T ≅ splitTorus S I` of a maximal split torus has
   `Nat.card I = splitRank G`.

No perfectness, characteristic, infiniteness, splitness or local-field
hypothesis is used. Neither conjugacy nor attainment of the split rank is
assumed.

The module imports the two intermediate proofs from
[SmoothMaximalSplitTorusConjugacyProof](SmoothMaximalSplitTorusConjugacyProof.md).
The identical declarations in the independently accepted contributions are
consolidated there; their statements and the final assembly are unchanged.

## `splitTorusIntoPseudoParabolic`

This proves the published `SplitTorusIntoPseudoParabolicStatement.{u}`: every
split subtorus of a smooth connected affine group is conjugate by a rational
point into any pseudo-parabolic subgroup. It applies the published conditional
`splitTorusIntoPseudoParabolic_of_components` to five proofs:

- `smoothSubgroupQuotientExistence`, the quotient `G/P`;
- `pseudoParabolicSubgroupStructure`, smoothness, connectedness and
  affineness of `P`;
- `pseudoParabolicQuotientPseudoComplete`, pseudo-completeness of `G/P`;
- `splitSolvablePseudoCompleteFixedPoint`, fixed points of split solvable
  groups;
- `pseudoParabolicQuotientRationalLifting`, rational lifting (module
  `Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof`).

All five inputs are included in the integrated Library.
The split torus acts on `G/P` and has a rational fixed point there. A rational
lift `g` of that point conjugates the torus into `P`.

## `smoothMaximalSplitTorusConjugacy`

This proves the published `SmoothMaximalSplitTorusConjugacyStatement.{u}`:
maximal split tori of a smooth connected affine group over any field are
conjugate by a rational point. It applies the published conditional
`smoothMaximalSplitTorusConjugacy_of_solvable_of_envelope_of_structure_of_containment`
to the published `solvableMaximalSplitTorusConjugacy`,
`noProperPseudoParabolicSolvableEnvelope` and
`pseudoParabolicSubgroupStructure`, and to `splitTorusIntoPseudoParabolic`.
The published assembly performs Noetherian induction on closed subgroups. If
`G` has a proper pseudo-parabolic subgroup, every split torus is conjugated into
it. Otherwise all split tori lie in one smooth connected solvable closed
subgroup, where the solvable conjugacy theorem applies.

## `maximalSplitTorusConjugacy`

The published `maximalSplitTorusConjugacyStatement_of_extension_conjugacy`
reduces both clauses to two inputs.

- **Maximal extension.** Every closed split torus `j : splitTorus S J ⟶ G`
  factors through a maximal split torus. The published
  `exists_maximalSplitTorus_extension` supplies this from affineness and
  smoothness of `G`, both parts of `IsConnectedReductive G`.
- **Conjugacy.** Any two maximal split tori are `SubgroupConjugate`. This
  follows from `smoothMaximalSplitTorusConjugacy`, since a connected reductive
  group is smooth, affine and connected (`hG.smooth`, `hG.isAffineHom`,
  `hG.connectedSpace`).

Inside the reduction, conjugacy gives the first clause directly. For the
second, `IsMaximalSplitTorus.card_eq_splitRank_of_extension_conjugacy` bounds
`splitRank G`, the supremum of `Nat.card J` over closed split tori `𝔾ₘ^J ⟶ G`.
Every such torus extends to a maximal split torus, which by conjugacy is
isomorphic to the given one. A monomorphism of split tori bounds the number of
factors. Hence the supremum equals `Nat.card I` for every finite splitting.

## Sources

The target is Borel–Tits, *Groupes réductifs* (1965), 4.21 and 4.23, and
Milne, *Algebraic Groups* (2017), Theorem 25.10, as documented in the
statement's paired Markdown. The implemented route goes through the
smooth-group theorem Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Theorem C.2.3, and Lemmas C.2.1–C.2.2 (printed pp.592–594),
recorded in the paired Markdown of `SmoothMaximalSplitTorusConjugacyStatement`,
`SplitTorusIntoPseudoParabolicStatement` and
`PseudoParabolicQuotientRationalLiftingStatement`.
