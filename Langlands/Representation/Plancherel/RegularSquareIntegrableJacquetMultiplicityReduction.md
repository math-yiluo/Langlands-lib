# A reduction of actual regular square-integrable Jacquet multiplicity

Author: Worker 1597.

This internal assembly reduces the Prop target
`RegularSquareIntegrableJacquetMultiplicityStatement`, which was submitted for
the same task, to five Prop statements
already in the Library, none of them proved there:

- `RepresentedGeometricLemmaStatement` (Renard VI.5.1 for represented
  parabolics): a finite enumeration of double cosets, representatives,
  intersection data and a gluing of `r_Q ∘ i_P` from the geometric-lemma
  pieces;
- `TemperedSquareIntegrableUnitaryPartStatement` (Renard VII.2.4): for a
  tempered representation with a central character, square integrability
  modulo the center is equivalent to vanishing of the unitary Jacquet part
  along every proper parabolic;
- `ArbitraryParabolicQuotientCompactStatement`: compactness of `G(F)/P(F)`
  for every represented parabolic;
- `SquareIntegrableNormalizedTemperedStatement` (Renard VII.2.1, Remark 2):
  square integrability modulo the center implies normalized-exponent
  temperedness;
- `ArbitraryParabolicJacquetAdmissibilityStatement`: the represented Jacquet
  functor preserves admissibility.

`RegularSquareIntegrableJacquetMultiplicityReductionStatement` is the
Prop-valued definition of the implication from these five propositions, at
the universes `u` (field and groups) and `uV` (inducing carrier), to the
unchanged `RegularSquareIntegrableJacquetMultiplicityStatement.{u, uV}`.
The companion theorem `regularSquareIntegrableJacquetMultiplicity_of_statements`
proves the implication. Nothing here proves any of the five inputs, and this
module is not a proof of the target or of the generic-irreducibility task.

The motivating source is the multiplicity consequence of Waldspurger 2003,
Corollary III.7.3 (printed p.276), registered as
`waldspurger-2003-plancherel`; see `RegularJacquetMultiplicityStatement.md`
for the target's provenance. The implemented route differs from the source.
Waldspurger decomposes the weak Jacquet module (III.7.2, III.7.3). Here only
Hom spaces are bounded: along the geometric-lemma filtration, a Hom length is
at most the sum of the Hom lengths of the graded pieces.

## Dependencies

Besides published Library modules, the module imports the supporting
modules `ParabolicRepresentedComparison`, `ParabolicJacquetUnitaryRestriction`,
`ParabolicSquareIntegrableModCenter`, `SelfUnitaryPieceMultiplicity`,
`LeviUnitaryGluedHomBound` and the target `RegularJacquetMultiplicityStatement`,
submitted for the same task.

## Helper results

- `isNormalizerRegular_of_iso`: `IsNormalizerRegular` depends only on the
  isomorphism class of the smooth representation. An isomorphism `σ ≅ σ'`
  also identifies the normalizer conjugates.
- `isNormalizerRegular_pullback_subgroupCongr`: regularity is unchanged by
  identifying equal subgroups of the ambient group.
- `isNormalizerRegular_leviPoints_pullback`: regularity of a representation
  `π` of the literal Levi `parabolicLeviPointSubgroup p l` passes to the
  representation of the represented Levi image `pointImage (l ≫ p)`. That
  representation is obtained by pulling `π` back to `M(F)` and then to the
  image. The proof uses `pullbackPullbackIso` and the equality
  of the two subgroups.
- `leviTwistedInduction_obj_isAdmissible`: assume compact actual parabolic
  quotients and continuity of the literal Levi projection. Then the literal
  Levi-twisted induction of an admissible representation is admissible. The
  proof transports along the published `normalizedInductionLeviTwistIso`,
  using `parabolicRadical_isUnimodular`, and applies
  `normalizedInductionFunctor_obj_isAdmissible`.
- `representedJacquetInduction_isAdmissible`: if the literal induction is
  admissible, then so is the represented `r_P ∘ i_P` of the pulled-back
  representation. The proof uses the literal Jacquet admissibility
  `parabolicJacquet_obj_isAdmissible` and the identification
  `parabolicRepresentedJacquetInductionIso`.

## The bound

`jacquetInductionHom_rank_le_one_of_statements` works in the host target's
structural context, given the five inputs, connected reductivity, Hausdorff
`G(F)` and continuity of the literal Levi projection. Let `π` be an
irreducible representation of the literal Levi that is square-integrable
modulo the split-component image `C` and normalizer-regular. Then the literal
Jacquet Hom space `Hom(r_P(I_P π), π)` has rank at most one. The proof runs
as follows. Write `σ` for the pullback of `π` to `M(F)`.

1. `parabolicJacquetHom_rank_le_representedUnitary` bounds the
   literal rank by the Hom rank from the represented unitary Jacquet module
   of the represented induction of `σ` into `σ`. Its admissibility input
   comes from `leviTwistedInduction_obj_isAdmissible`.
2. `isSquareIntegrableModCenter_pullback_of_modCentralSubgroup` makes `σ`
   square-integrable modulo the full center for the Haar measure
   `Measure.haar` on `M(F)` modulo its center. `σ` is then tempered by
   `SquareIntegrableNormalizedTemperedStatement`. It is irreducible because
   the pullback is along a topological group isomorphism, and regular by
   `isNormalizerRegular_leviPoints_pullback`.
3. `RepresentedGeometricLemmaStatement`, applied with both parabolic triples
   equal to the inducing triple, supplies the double-coset enumeration, the
   representatives `z i`, the self-intersection data `D i` and the gluing.
4. `leviUnitaryJacquetInductionHomRank_le_one_of_doubleCosets`
   reduces the bound to two facts about the zero-real-part selected pieces:
   each has Hom length at most one, and a piece with nonzero Hom length has
   its representative in `P(F)`. Admissibility of the represented
   `r_P ∘ i_P` comes from `representedJacquetInduction_isAdmissible`.
5. `selectedPieceHomLength_le_one` and
   `mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero` give these
   two facts. Their inputs are a split component of each piece's Levi, from
   the published `splitComponentStatement`; Jacquet admissibility of `σ`
   along each piece's parabolic, from
   `ArbitraryParabolicJacquetAdmissibilityStatement` applied to `M`; the
   criterion `TemperedSquareIntegrableUnitaryPartStatement`; and quotient
   compactness.

`regularSquareIntegrableJacquetMultiplicity_of_statements` introduces the
target's binders and applies this bound.
