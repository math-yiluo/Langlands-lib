# Weyl conjugacy invariance of finite-length normalized induction: proof

Author: Worker 757.

The theorem `Langlands.Parabolic.wholeLeviInductionConjugacy` proves the
published proposition `Langlands.Parabolic.WholeLeviInductionConjugacy.{uF, uV, uW}`
from `Parabolic/WholeLeviConjugacyStatement`. The statement pair and its
imports are unchanged. The theorem is

```
theorem wholeLeviInductionConjugacy {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : WholeLeviInductionConjugacy.{uF, uV, uW} F T
```

with universe parameters `uF uV uW` and no further hypotheses. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

So for every rank `n` (including `0`), all block shapes `B C : BlockShape n`,
every permutation `w` with `ConjugatesLevi B C w`, every finite-length smooth
`σ` of the `B`-Levi (carrier in `uV`) and every finite-length smooth `τ` of the
`C`-Levi (carrier in `uW`) with `transport B C w hw σ ≃ τ`, the normalized
inductions `T.normalizedParabolicInduced B σ` and
`T.normalizedParabolicInduced C τ` have the same Jordan–Hölder factors with
multiplicities (`HaveSameJordanHolderFactors`). No admissibility,
cuspidality, irreducibility, tensor factorization, positive-rank or
minimal-representative premise is added. The hypothesis `τ.HasFiniteLength`
of the statement is not needed by the proof.

## Mathematical argument

Write `i_B` for normalized parabolic induction from the standard upper block
parabolic of `B`, and `wσ := transport B C w hw σ`, so `(wσ)(m) = σ(P_w⁻¹ m P_w)`.
Since `wσ ≃ τ` gives `i_C(wσ) ≃ i_C(τ)`, it suffices to compare `i_B(σ)`
with `i_C(wσ)`.

1. **At most one block.** If `B` has at most one block, then `C = B` and `w`
   maps every block of `B` to itself, so `P_w` lies in the `B`-Levi. Transport
   by `w` is then conjugation by a Levi element, hence `wσ ≃ σ` by the
   operator `σ(P_w)`. So `i_B(σ) ≃ i_C(τ)`. By the published finite-length
   preservation of normalized induction, `i_B(σ)` has a composition series,
   and equivalent representations have the same factors.

2. **Reduction to irreducible `σ` (positive rank).** Choose a composition
   series of `σ`. Transport changes only the acting group, along the group
   isomorphism `(leviConjugation B C w hw)⁻¹`, so the same subspaces form a
   composition series of `wσ`, whose graded pieces are exactly the transports
   of the graded pieces of `σ`. Normalized induction is exact on smooth
   representations, so inducing the two series gives filtrations of `i_B(σ)`
   and `i_C(wσ)` whose `i`-th graded pieces are `i_B(σ_i)` and `i_C(wσ_i)`,
   with `σ_i` the `i`-th (irreducible) graded piece of `σ`. If each pair
   `i_B(σ_i)`, `i_C(wσ_i)` has the same factors, refining both filtrations
   gives the claim.

3. **Irreducible `σ` (positive rank).** Write `w = v b` with `v` the minimal
   representative of the coset `w · W_B` and `b` in the block Weyl group
   `W_B` (permutations preserving every block of `B`). As in step 1,
   transport by `b` is equivalent to `σ`, so `wσ ≃ vσ`. A minimal conjugating
   permutation is the canonical block reordering: `C = B.permute e` and
   `v = B.blockPermutation e` for a permutation `e` of the block labels. An
   irreducible representation of the Levi is admissible, and so `σ ≃ ⊗_i A_i`
   with irreducible admissible `A_i`. Transport by the canonical reordering
   sends `⊗_i A_i` to `⊗_i A_(e i)` on `B.permute e`. It remains to show that
   the products `A_0 × ⋯ × A_(k-1)` and `A_(e 0) × ⋯ × A_(e (k-1))` have the
   same factors.

4. **Arbitrary reorderings.** The adjacent transpositions generate the
   permutations of the block labels as a monoid, and having the same factors
   is transitive. So it suffices to treat one adjacent transposition, applied
   to an arbitrary family of irreducible admissible factors on an arbitrary
   shape.

5. **One adjacent transposition of positions `j, j+1`.** Let `D` be the shape
   obtained by merging blocks `j` and `j+1`. Induction in stages gives
   `A_0 × ⋯ × A_(k-1) ≃ i_D(⊗_m Π_m)`, where `Π_j = A_j × A_(j+1)` and every
   other `Π_m` is the induction of one factor from the one-block shape. For the
   swapped product, `≃ i_D(⊗_m Π'_m)` with `Π'_j = A_(j+1) × A_j` and the same
   one-block inductions elsewhere. Block `j`: `Π_j` and `Π'_j` have the same
   factors by the published irreducible two-factor case of Zelevinsky's
   Theorem 1.9. Other blocks: step 1. All `Π_m` and `Π'_m` are admissible
   (normalized induction preserves admissibility), so the external tensor
   products `⊗_m Π_m` and `⊗_m Π'_m` have the same factors by the published
   factor matching for finite external tensors over `p`-adic Levis. Finally,
   normalized induction from `D` preserves matching of factors when both
   induced outputs have finite length. Both outputs are equivalent to products
   of irreducible admissible factors; such an external tensor is irreducible
   (admissible Schur lemma), so its induction has finite length.

6. **Rank zero.** A shape of rank `0` has no blocks, so step 1 applies.

The argument uses neither the Langlands classification nor any segment or
multisegment result. It does not follow the printed proof of Ban–Jantzen,
Proposition 4.1(3) (see Sources).

## Normalization

The proof never unfolds the half-modulus twist. Every comparison is an
equivalence or a theorem stated for the actual normalized inductions
`T.normalizedParabolicInduced` and `T.normalizedProductInduced`, so the
normalization is handled inside those published results:

- Induction in stages, `orderedRefinementTensorInductionEquiv`
  (`Parabolic/OrderedRefinementTensorInduction`), is an actual equivalence
  between `T.normalizedProductInduced B A` and the normalized induction from
  `D` of the external tensor of the normalized inner products. It is built on
  `orderedRefinementInductionEquiv` (`Parabolic/OrderedRefinementInduction`),
  which composes the published normalized induction in stages
  (`Parabolic/RefinementInductionTransitivityProof`) with
  `Parabolic/RefinementCoordinatesNormalizationProof`, where the half-modulus
  characters of the refined and ordinary parabolics are matched.
- Exactness enters through `normalizedInductionFiltration` and its graded
  equivalences (`Parabolic/InductionFiltration`), stated for normalized
  induction and proved from the published surjectivity of smooth induction.
- The two-factor theorem, finite-length preservation, admissibility
  preservation and the factor-matching theorem for induction are all stated
  for the same normalized induction.

## Actual transport

The transport in the target is inverse conjugation,
`transport B C w hw ρ = ρ ∘ (leviConjugation B C w hw)⁻¹`. The proof works
with it directly:

- `transportWeylEquiv` (`CuspidalSupport/AssociationReduction`) gives
  `transport B B b hb ρ ≃ ρ` for `b` in `blockWeyl B`, through the action of
  the Levi element whose embedding is the permutation matrix of `b`.
- `transport_transport` (same module) identifies the transport along `b`
  followed by the transport along `v` with the transport along `v * b = w`;
  `transportEquiv` transports equivalences.
- `blockPermutationTensorEquiv` (`CuspidalSupport/BlockPermutationTensor`)
  identifies the transport of `B.blockTensor ρ` along
  `B.blockPermutation e` with `(B.permute e).blockTensor (fun i => ρ (e i))`.
- In step 2, a composition series of `σ` is pulled back along the surjective
  group homomorphism `(leviConjugation B C w hw).symm` by
  `FiniteTensor.FactorMatchingProof.filtrationComp`
  (`Filtration/FactorMatchingPullback`). Its graded pieces are the transported
  graded pieces of `σ`; the equivalence `gradedComp` is the identity linear map.

## Universes and topology

The universes `uF`, `uV`, `uW` stay independent. The source `σ`, its
composition factors, their transports and the block factors `A_i` of step 3
have carriers in `uV`. The inner normalized inductions of step 5 and all
induced representations of `σ`-data have carriers in `max uF uV`. The
irreducible two-factor theorem is used at `.{uF, uV}`, external tensor factor
matching and induction factor matching at the carrier universes
`max uF uV`, and finite-length preservation at `.{uF, uV}`. The target
representation `τ` (carrier in `uW`) enters only once, at the end, through
`T.normalizedParabolicInducedEquiv C φ` from the given `φ : wσ ≃ τ`; in step 3
it enters similarly through the composite equivalence
`τ ≃ (B.permute e).blockTensor (fun i => A (e i))`. All topology is the
supplied `T.topology` with `T.generalLinearTopologicalGroup` at the relevant
ranks. Proving that the transport of a smooth representation is smooth
(`isSmooth_transport`) needs the topological ring structure of `F.Carrier`,
which the proof installs from `T.valuativeRel` and `T.localField`.

## Rank zero and small shapes

The final theorem splits on `n`. For `n = 0`, `B.length ≤ n = 0`
(`BlockShape.length_le`), so `factors_of_length_lt_two` applies (step 1). It
uses only finite-length preservation of normalized induction, which holds in
every rank, and needs no positive-rank input. The positive-rank inputs
`padicLeviAdmissibleFactorization` and `FiniteTensor.padicExternalTensorFactors`
require `0 < n` and are used only for `n > 0`. Step 1 also covers every rank
when `B` has one block.

## Declarations

All auxiliary declarations are in the namespace
`Langlands.Parabolic.WholeLeviConjugacyProof`.

- `eq_and_mem_blockWeyl_of_length_lt_two`: if `ConjugatesLevi B C w` and
  `B.length < 2`, then `C = B` and `w ∈ blockWeyl B`. It uses
  `TotalConjugatingCount.length_eq` (equal block numbers),
  `BlockShape.ext_of_size` for zero blocks and `eq_of_length_eq_one` for one
  block; block membership holds because all block indices are `0`.
- `factors_of_length_lt_two`: step 1. Finite length of
  `T.normalizedParabolicInduced B σ` comes from
  `(normalizedParabolicFiniteLength F T).1`, a composition series from
  `exists_hasSimpleFactors_of_hasFiniteLength`, and the conclusion from
  `FactorMatchingProof.haveSameJordanHolderFactors_of_equiv` applied to
  `T.normalizedParabolicInducedEquiv B ((transportWeylEquiv w hb hw σ).symm.trans φ)`.
- `isIrreducible_external_of_admissible`: a finite external tensor of
  irreducible admissible smooth factors is irreducible
  (`FiniteTensor.isIrreducible_external` with the scalar endomorphisms from
  `admissibleSchur_scalarEndomorphism`).
- `productInduced_finiteLength`: the normalized product of irreducible
  admissible factors has finite length (previous lemma,
  `SmoothRep.hasFiniteLength_of_isIrreducible` and finite-length
  preservation).
- `CuspidalSupport.refinedInnerInductionObjects D S C`: the existing smooth
  objects formed by normalized inner induction in each block of `D`, now
  imported from `Parabolic/RefinedInnerInductionObjects`. The construction
  was moved unchanged out of `CuspidalSupport/AdjacentMatchingAssembly`;
  that conditional assembly remains outside this module's imports.
- `Classification.adjacentSwap_zero_eq_revPerm`: the already imported
  two-block identity identifying the adjacent swap with `Fin.revPerm`.
- `innerTensor`, `reverseTensor`: the external tensors of the original factors
  inside each merged block of `B.adjacentMerge j hj`, in the original and in
  the reversed inner order (refinements `B.adjacentRefinement j hj` and
  `B.adjacentReverseRefinement j hj`).
- `reverseTensorFactors_eq`: the regrouped factors that
  `orderedRefinementTensorFactors` assigns to the swapped product are equal to
  `reverseTensor` (via `adjacentBlockEquiv_rev` and the rank casts
  `adjacentReverse_size`; private helper `family_rankCast_eq`). The private
  `stagesFactorsCast` rewrites an equivalence along this equality.
- `innerInductions_matching`: the inner products match blockwise. For the
  merged block (`m = j`, two inner blocks) it applies
  `Classification.twoFactorProductConstituentCommutativity` and rewrites its
  swap by `adjacentSwap_zero_eq_revPerm`. For the other blocks (one inner
  block) it applies `factors_of_length_lt_two` with the block reordering
  `blockPermutation Fin.revPerm`, `conjugatesLevi_blockPermutation` and the
  equivalence `blockPermutationTensorEquiv`.
- `innerExternalTensors_matching`: the external tensors of the inner products
  match, by `FiniteTensor.padicExternalTensorFactors` (requires `0 < n`). Its
  admissibility premises come from `normalizedInductionAdmissibility` and
  `FiniteTensor.isAdmissible_external`.
- `matchingThroughStages` (private, with private `finiteLength_throughEquiv`):
  given equivalences of two representations with outer normalized inductions
  from `D` of matching external tensors, and finite length of both
  representations, they have the same factors
  (`normalizedInductionFactorMatchingTheorem`, then
  `haveSameJordanHolderFactors_transport`). Finite length is moved along an
  equivalence by `FiniteLengthAssembly.finiteLength_of_surjective`.
- `adjacentProduct_factors`: step 5, combining the two stages equivalences
  `orderedRefinementTensorInductionEquiv` (for `B` with
  `B.adjacentBlockEquiv`, `adjacentBlock_size`, `adjacent_index`, and for
  `B.permute (B.adjacentSwap j hj)` with `adjacentReverse_size`,
  `adjacentReverse_index`) with the previous lemmas.
- `permutedProducts`: step 4, by `Submonoid.induction_of_closure_eq_top_right`
  over `closure_adjacent_swaps`, with `haveSameJordanHolderFactors_trans`.
  The base case `e = 1` uses the private `haveSameJordanHolderFactors_self`
  (a composition series from finite length, via
  `LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`).
  Since `(B.permute x).permute s` is definitionally `B.permute (x * s)`, the
  inductive step applies `adjacentProduct_factors` to the shape `B.permute x`.
- `irreducible_factors`: step 3 for `0 < n`. It uses
  `minimalConjugatingCosets`, `conjugatesLevi_of_blockIndex`,
  `exists_blockMap_of_conjugatesLevi`, `eq_blockPermutation_of_blockIndex`,
  `irreducibleLeviAdmissibility`, `padicLeviAdmissibleFactorization`,
  `blockPermutationTensorEquiv`, `permutedProducts` and
  `haveSameJordanHolderFactors_transport` along
  `T.normalizedParabolicInducedEquiv`.
- `finiteLength_factors`: step 2 for `0 < n`. It uses
  `exists_hasSimpleFactors_of_hasFiniteLength`, `filtrationComp`,
  `normalizedInductionFiltration`, `normalizedInductionFiltrationGradedEquiv`
  (for `σ`) and `nonempty_normalizedInductionFiltrationGradedEquiv` with
  `gradedComp` (for `wσ`). Smoothness of the graded pieces comes from
  `isSmooth_of_injective` and `isSmooth_of_surjective`, and of their
  transports from `isSmooth_transport`. It then applies `irreducible_factors`
  to each piece and `gradedJordanHolderRefinement` with the identity index
  permutation, and finishes with `T.normalizedParabolicInducedEquiv C φ`.
- `Langlands.Parabolic.wholeLeviInductionConjugacy`: the target. It
  introduces the data, discards `τ.HasFiniteLength`, and uses
  `factors_of_length_lt_two` for `n = 0` and `finiteLength_factors` for
  `n > 0`.

The module sets `backward.isDefEq.respectTransparency.types false`, as do the
imported stages modules. It has no `sorry`, no new axioms and no change of
`maxHeartbeats`.

## Imports and independence

Direct imports (26): `Parabolic/RefinedInnerInductionObjects`; the target `Parabolic/WholeLeviConjugacyStatement`;
`Parabolic/ProductReversalFactorsProof` (only for
`exists_hasSimpleFactors_of_hasFiniteLength`; `twoBlockProductReversalFactors`
is not used); `Parabolic/FiniteLengthFunctorProof`;
`Parabolic/InductionFactorMatchingProof`; `Parabolic/InductionFiltration`;
`Parabolic/OrderedRefinementTensorInduction`;
`Parabolic/NormalizedAdmissibilityProof`;
`Classification/TwoFactorProductConstituentCommutativityProof`;
`Classification/FiniteLengthProof` (only for the generic
`FiniteLengthAssembly.finiteLength_of_surjective`);
`CuspidalSupport/AdjacentMergedTensor`, `AssociationReduction`,
`BlockPermutationTensor`, `IrreducibleLeviAdmissibilityProof`,
`LeviAdmissibleFactorizationProof`, `MinimalConjugatingCosetsProof`,
`TotalConjugatingCountProof`; `Tensor/FactorMatchingProof`,
`Tensor/FiniteProperties`; `Filtration/FactorMatchingPullback`,
`GradedRefinementProof`, `JordanHolderComparisonProof`,
`JordanHolderTransportProof`; `Smooth/Transfer/SubquotientProof`,
`Smooth/IrreducibleRealization` and `Smooth/Schur/Proof`.

The `CuspidalSupport` modules are used only for their general results on
shapes, conjugating permutations, transport, Levi admissibility and tensor
factorization. Their cuspidal theorems (adjacent assembly, association of
cuspidal data) are not used, and `CuspidalSupport/AdjacentMatchingAssembly`
is not imported.

Main proved inputs and their authors: finite-length preservation
(`FiniteLengthFunctorProof`, Worker 395); the irreducible two-factor case
(`TwoFactorProductConstituentCommutativityProof`, Worker 763); irreducible
Levi admissibility (Worker 171); admissible Levi factorization (Worker 161);
induction factor matching (Workers 250 and 181); graded refinement
(Worker 122); minimal conjugating cosets (Worker 165); block permutation
tensors (Worker 289); association reduction helpers (Worker 242);
admissibility of normalized induction (Workers 162 and 172); normalized
induction in stages (`RefinementInductionTransitivityProof`, Worker 162).

The transitive closure of this module's imports in the workspace Library
(base commit `b22e185743f7c318f709e14e422801f4360105d5`) was checked file by
file. It has 695 `Langlands` modules. None of them is, or proves, an excluded
result: analytic segment classification
(aca8805b-054f-4d56-8045-12db7f623404), special-head multisegment exhaustion
(3bfb61fa-1129-4fc9-83fd-7fcfec22106e), ordered strong-head existence
(ebea9a8a-9b21-4208-aa31-98c2dea1f8a3), quotient coverage
(20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584), tempered block uniqueness
(52e97845-36bb-457d-b76f-70753334b88c), `SquareIntegrableLanglandsClassification`
(1cb45da2-7007-4351-a694-594fb148b8d1), square-integrable exhaustion
(cd8ab97c-0b78-4bce-97c4-d307a28159a4) or regular exhaustion
(bf433f0a-921a-428c-b0c0-6475438125ac). No module name or Lean file in the
closure refers to these results; the only match of the search patterns is the
definition `IsSegmentHead` in `Classification/Segments`. The excluded task
IDs occur only in the Markdown of
`Classification/TwoFactorProductConstituentCommutativityStatement`,
`CuspidalSupport/IrreducibleLeviAdmissibilityProof`,
`CuspidalSupport/MinimalRefinedJacquetProof`,
`Parabolic/WholeLeviConjugacyStatement`, `Smooth/Admissibility/ExactProof`,
`Smooth/Admissibility/FiniteLengthProof`, `Smooth/FiniteLengthGrothendieck`
and `Smooth/FiniteLengthGrothendieckFunctor`, each time in a statement that
they are not inputs.

The closure contains 16 `Classification` modules: `ConstituentRelations` and
`Segments` (definitions and their basic lemmas); `Supercuspidal`,
`SupercuspidalTwist`, `SupercuspidalSupport`,
`SupercuspidalContragredientStatement`, `SupercuspidalContragredientAux`;
`IrreducibleProductEmbedding` and its statement;
`NormalizedProductFiniteLengthStatement` and
`NormalizedProductFiniteLengthProof`; `IrreducibleProductFiniteLengthProof`;
`FiniteLengthStatement` and `FiniteLengthProof` (finite length of admissible
finitely generated representations); and the two modules of the irreducible
two-factor case. None contains an excluded conclusion. The irreducible
two-factor proof follows Zelevinsky's route through the Gelfand–Kazhdan
involution, so the closure also contains the contragredient modules
`Smooth/Contragredient/*`.

## Sources

- D. Ban and C. Jantzen, *The Langlands quotient theorem for finite central
  extensions of p-adic groups II: intertwining operators and duality*,
  Glasnik Mat. 51(71) (2016), 153–163, Proposition 4.1(3), printed p.158
  (registered source `ban-jantzen-2016-duality`). The target is the `GL_n`,
  finite-length form of this identity (see the statement Markdown). Its printed
  proof relies on the Langlands classification; this proof does not follow it.
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ÉNS (4) 13 (1980),
  165–210, Theorem 1.9, printed p.174 (registered source
  `zelevinsky-1980-induced-ii`). Its irreducible two-factor case enters through
  the published `Classification.twoFactorProductConstituentCommutativity`.
  The reduction from arbitrary block permutations and whole-Levi finite-length
  data to that case (steps 1–6) is the route implemented here.
