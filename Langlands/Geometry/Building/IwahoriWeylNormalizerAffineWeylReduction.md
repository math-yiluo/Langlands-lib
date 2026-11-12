# The Iwahori–Weyl exact sequence and chamber splitting from KP Theorem 7.5.3(2)

`IwahoriWeylNormalizerAffineWeylReductionStatement.{u}` is the implication from
the published `SimplyConnectedNormalizerAffineWeylStatement.{u}` (the range part
of KP Theorem 7.5.3(2): `N(F) ∩ G(F)^♮` acts on the apartment through exactly
`W(Ψ)`) to the conjunction of the two unchanged published targets
`IwahoriWeylExactSequenceStatement.{u}` (KP Theorem 7.8.1(1)) and
`IwahoriWeylChamberSplittingStatement.{u}` (KP 7.8.2).
`iwahoriWeylNormalizerAffineWeylReduction` proves this implication.

The range statement remains an explicit premise. This unit does not prove
either target without it; it shows that the range statement is the only
missing input of the published assembly.

## Comparison with the published assembly

`iwahoriWeylExactSequenceStatement_of_prerequisites` in
`IwahoriWeylExactSequenceReduction` takes four premises: KP Lemma 2.6.24
(`UnramifiedZeroPointsIndependenceStatement`), KP Fact 2.6.22
(`SimplyConnectedCentralizerProductStatement`), the range statement, and KP
Corollary 2.6.28 for every zero datum. Here the three premises other than the
range statement are replaced by published proofs:

- Both normalities, `Z(F)^0 ⊴ N(F)` and `G(F)^0 ⊴ G(F)`, come from
  `ParahoricBuildingData.normal_normalizerZero` and
  `ParahoricBuildingData.normal_zeroSubgroup` in
  `ZeroSubgroupCommutatorNormality`. `G(F)^0` contains `G(F)^♮`, which contains
  every commutator of `G(F)`, so `G(F)^0` is normal; normality of `Z(F)^0` then
  follows from the cover comparison. This route does not use KP Lemma 2.6.24,
  which remains unproved and is not claimed here.
- KP Fact 2.6.22 is the published theorem
  `Langlands.GroupScheme.simplyConnectedCentralizerProduct`.
- KP Corollary 2.6.28 for the data of `P` is
  `ParahoricBuildingData.centralizerZeroIntersection`, defined in this module
  as `centralizerZeroIntersection_of_coverImage` applied to the published
  unconditional cover-image containment
  `ZeroSubgroupDatum.coverImageCentralizerNormKernel`.

## The proof

`ParahoricBuildingData.iwahoriWeylExactSequence_of_normalizerAffineWeyl`
proves `P.IwahoriWeylExactSequence` for actual data `P` satisfying the
apartment axioms, given the range statement `hW`. It supplies the two
normalities above, and then the three components of the exact sequence from
the published lemmas of `IwahoriWeylExactSequenceReduction` and
`IwahoriWeylQuotientLemmas`:

- the action-compatible isomorphism `P.affinePart ≃* W(Ψ)` from
  `exists_affinePart_equiv_of_action`, whose three inputs are: every
  `n ∈ N(F) ∩ G(F)^0` acts through `W(Ψ)`
  (`normalizerAffineEquiv_mem_affineWeylGroup hP hW`), the kernel of this action
  is `Z(F)^0` (`normalizerAffineEquiv_eq_one_iff` with Corollary 2.6.28), and
  every element of `W(Ψ)` is realized
  (`exists_normalizerZeroComponent_normalizerAffineEquiv_eq hP hW`);
- the kernel of `W̃^0 → G(F)/G(F)^0` is the affine part
  (`toComponents_ker_eq_affinePart`);
- this map is surjective (`toComponents_surjective` with Fact 2.6.22).

The global theorem applies this to every `F`, `G` and `P` of
`IwahoriWeylExactSequenceStatement`, and then obtains
`IwahoriWeylChamberSplittingStatement` from the published unconditional
`iwahoriWeylChamberExactSequenceReduction`, which uses the proved simple
transitivity of `W(Ψ)` on chambers.

Both statements retain the arbitrary field universe `u`, the actual
normalizer, centralizer, zero subgroups and apartment, the original apartment
axioms (including the corrected Chapter 7 AS 5) and the full component part.
No normality, kernel, surjectivity or chamber hypothesis is added.

## Provenance

The provenance is internal: a composition of published theorems. The
contextual sources are KP Theorem 7.8.1(1), 7.8.2 and Theorem 7.5.3(2), as
documented in the unchanged `IwahoriWeylStatement` and
`SimplyConnectedNormalizerAffineWeylStatement` pairs. The normality route via
commutators differs from KP's route via Lemma 2.6.24.
