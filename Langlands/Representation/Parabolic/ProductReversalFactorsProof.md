# Composition-factor commutativity of two-factor products of finite length

Author: Worker 757.

The theorem `Langlands.Parabolic.twoBlockProductReversalFactors` proves the
published proposition
`Langlands.Parabolic.TwoBlockProductReversalFactors.{uF, uV}` from
`Parabolic/ProductReversalFactorsStatement`. This is Zelevinsky (1980),
Theorem 1.9 (printed p.174), for two smooth factors of finite length. The
statement is not changed, and the theorem has no hypotheses. The proof derives
it from the irreducible two-factor case, the published proposition
`Langlands.Classification.TwoFactorProductConstituentCommutativity.{uF, uV}`
(`Classification/TwoFactorProductConstituentCommutativityStatement`). That
case is supplied by its published proof
`Langlands.Classification.twoFactorProductConstituentCommutativity`
(`Classification/TwoFactorProductConstituentCommutativityProof`).

The module has two layers. The conditional reduction
`twoBlockProductReversalFactors_of_irreducible` takes the irreducible case as
an explicit hypothesis. The final theorem `twoBlockProductReversalFactors`
supplies that hypothesis with the published proof of the irreducible case.

## Mathematical argument

Let `π₁` and `π₂` have finite length. Choose composition series of both. Their
external tensor product `π₁ ⊠ π₂`, a representation of the Levi subgroup
`GL_a × GL_b`, then has a finite filtration. Its successive quotients are the
products `σ ⊠ τ` over all pairs of a composition factor `σ` of `π₁` and a
composition factor `τ` of `π₂`, each pair occurring exactly once. Normalized
parabolic induction is exact, so inducing this filtration gives a filtration of
`π₁ × π₂` whose successive quotients are the products `σ × τ`. Likewise,
`π₂ × π₁` has a filtration with successive quotients `τ × σ`, indexed by the
same pairs, now listed in the opposite order. By the irreducible case,
`σ × τ` and `τ × σ` have the same composition factors with multiplicities.
Refining the two filtrations by the composition series of their matched
successive quotients gives composition series of `π₁ × π₂` and `π₂ × π₁` with
matched factors.

The argument does not depend on the number of blocks or on the permutation.
The Lean proof therefore runs it for an arbitrary block shape `B` and an
arbitrary permutation `σ` of its blocks (`productPermutationFactors_of_irreducible`),
and specializes to two blocks at the end.

This route differs from the one suggested in the task. That route uses tensor
factor matching (`FiniteTensor.PadicExternalTensorFactorsTheorem`) and
`Parabolic.normalizedInductionFactorMatchingTheorem`, followed by direct sums.
The route here needs neither. The reduction also does not use finite length
of products of irreducible factors (`Classification.IrreducibleProductFiniteLength`,
task 0717fd42-d711-4f42-8269-f6ae4c8da1e9), because the graded-refinement
theorem needs only matched Jordan–Hölder factors of the graded pieces. The
irreducible-case conclusion `HaveSameJordanHolderFactors` already contains
actual composition series of `σ × τ` and `τ × σ`. Admissibility of the
factors is not used either. The imported proof of the irreducible case does
use `IrreducibleProductFiniteLength` internally; that is part of its own
proof, not of the reduction here.

## Declarations

- `exists_hasSimpleFactors_of_hasFiniteLength A h`: a smooth representation `A`
  with `A.HasFiniteLength` has an actual composition series, that is, an
  `ObjectRepFiltration (Rep.of A.representation) r` with `HasSimpleFactors`.
  `HasFiniteLength` is `IsFiniteLength` of the group-algebra module. Mathlib's
  `isFiniteLength_iff_exists_compositionSeries` gives a module composition
  series from `⊥` to `⊤`, and
  `LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
  (`Filtration/LengthCriterionProof`) turns it into an actual one.

- `productPermutationFactors_of_irreducible F T B σ`: for every block shape
  `B : BlockShape n` and every `σ : Equiv.Perm (Fin B.length)`, under
  `T.topology`, suppose that for every family `C` of irreducible block
  factors, `(T.normalizedProductInductionFunctor B).obj C` and
  `(T.normalizedProductInductionFunctor (B.permute σ)).obj (fun i => C (σ i))`
  satisfy `HaveSameJordanHolderFactors`. Then the same holds for every family
  `A` of finite-length block factors. The proof:
  1. `choose` composition series `s i` of length `r i` of every factor `A i`
     (previous lemma).
  2. `FiniteTensorFiltration.exists_external` (`Tensor/ProductFiltration`),
     applied once to `A` with the `s i` and once to `fun i => A (σ i)` with the
     `s (σ i)`, gives filtrations `f` (length `N`) and `f'` (length `N'`) of
     the two actual external tensor products. It also gives bijections
     `E : Fin N ≃ ∀ i, Fin (r i)` and `E' : Fin N' ≃ ∀ i, Fin (r (σ i))` such
     that graded piece `j` is equivalent to the external tensor product of the
     chosen graded pieces `E j i`.
  3. `Φ := Equiv.piCongrLeft' _ σ.symm` reindexes choices, with
     `Φ x i = x (σ i)` by `rfl`. `Fintype.card_congr` along
     `E.trans (Φ.trans E'.symm)` gives `N' = N`. After `subst`, the index
     permutation is `e := E.trans (Φ.trans E'.symm)`, so that `E' (e j) = Φ (E j)`.
  4. The graded pieces of composition series are smooth: they are quotients
     of subrepresentations of smooth representations (`isSmooth_of_injective`
     with `FactorMatchingProof.subrepInclusion`, then `isSmooth_of_surjective`
     with the graded projection). For each `j`, the irreducible family is
     `C j i := SmoothRep.of ((s i).gradedRepresentation (E j i)).ρ _`. It is
     irreducible because the `s i` have simple factors.
  5. `normalizedInductionFiltration` (`Parabolic/InductionFiltration`) induces
     `f` and `f'` to filtrations `indF` and `indF'` of the two normalized
     products. Here `T.normalizedProductInductionFunctor B` applied to `A`
     is by definition the normalized parabolic induction of
     `B.blockTensor fun i => (A i).representation`.
     `nonempty_normalizedInductionFiltrationGradedEquiv` identifies graded
     piece `j` of `indF` with the product of the family `C j`, and graded
     piece `e j` of `indF'` with the product of `fun i => C j (σ i)`.
     Smoothness of the external tensor products comes from
     `FiniteTensor.isSmooth_external`. This lemma uses the exactness of
     normalized induction proved in the Library from
     `Induction.smoothInductionSurjectivity`.
  6. The hypothesis on irreducible families, transported along these two
     equivalences by `haveSameJordanHolderFactors_transport`
     (`Filtration/JordanHolderTransportProof`), matches graded piece `j` of
     `indF` with graded piece `e j` of `indF'`.
  7. `gradedJordanHolderRefinement` (`Filtration/GradedRefinementProof`, the
     proof of `GradedJordanHolderRefinementStatement`) concludes.

- `twoBlockProductReversalFactors_of_irreducible hirr`: if the irreducible case
  `Classification.TwoFactorProductConstituentCommutativity.{uF, uV} F T` holds
  for every prime `p`, every `F : PadicField.{uF} p` and every
  `T : F.TopologicalData`, then `TwoBlockProductReversalFactors.{uF, uV}`
  holds. After introducing the data of the target, the proof sets
  `B := BlockShape.binary a b ha hb` and `A := fun i => Fin.cases π₁ (fun _ => π₂) i`,
  proves finite length of each `A i` by `Fin.cases h₁ (fun _ => h₂)`, and
  applies `productPermutationFactors_of_irreducible` with
  `σ := B.adjacentSwap 0 Nat.one_lt_two`. The irreducible-case hypothesis is
  `hirr p F T (a + b) B rfl` (`B.length = 2` holds by `rfl`). The
  target's conclusion uses `T.normalizedProductInduced` directly, so it is
  definitionally the functor form used here.

- `twoBlockProductReversalFactors : TwoBlockProductReversalFactors.{uF, uV}`:
  the target. It applies `twoBlockProductReversalFactors_of_irreducible` to
  `fun _ _ F T => Classification.twoFactorProductConstituentCommutativity.{uF, uV} F T`.
  The irreducible-case theorem binds exactly `{p} [Fact p.Prime]`
  `(F : PadicField.{uF} p) (T : F.TopologicalData)`, so it fills the
  hypothesis directly. Its axioms are `propext`, `Classical.choice` and
  `Quot.sound`.

## Universes and topology

The field universe `uF` and the carrier universe `uV` are independent and are
kept unchanged from the target. The irreducible case is used at the same
`.{uF, uV}`. The irreducible families `C j` live in `uV`: they are quotients
of subrepresentations of the `A i`, carried by `uV` types. The external
tensor products of the `uV` carriers are again in `uV`. All topology is the
supplied `T.topology` with `T.generalLinearTopologicalGroup n`, as in both
statements. No universe transport or topology comparison is needed.

## Imports and dependency audit

Direct imports: the target `Parabolic/ProductReversalFactorsStatement`, the
irreducible-case statement `Classification/TwoFactorProductConstituentCommutativityStatement`
(a `Prop` definition only), its proof
`Classification/TwoFactorProductConstituentCommutativityProof`,
`Parabolic/InductionFiltration`, `Tensor/ProductFiltration`,
`Filtration/GradedRefinementProof`, `Filtration/JordanHolderTransportProof`
and `Filtration/LengthCriterionProof`.

The reduction's own inputs are general filtration, tensor and induction
results. Without the irreducible-case proof, their transitive closure is 104
`Langlands` modules. It contains no segment, multisegment, socle, head,
linked-gluing, classification-exhaustion, tempered, square-integrable,
genericity or Gelfand–Kazhdan module.

The irreducible case is owned by statement task
1b2016bd-4fd3-4ec6-a1b4-ec0788046ed9 and its proof task
afd5ae37-9c4e-44fe-897a-623bb2c92d91. This module imports that task's
published proof by its Lean name and does not reprove it. That proof follows
Zelevinsky's involution route, so the full closure contains the
Gelfand–Kazhdan and contragredient modules (`Smooth/Contragredient/*`),
`Classification/IrreducibleProductFiniteLengthProof`, cuspidal-support
modules and `Parabolic/InverseTransposeProductProof`. This is the intended
division of labour: the task assigns the analytic route to the irreducible
case and asks this module not to duplicate it.

The full transitive closure of this module, in the Library at commit
`91ab820b34fa295dd50fbdeb1389423b0f6478ea`, was checked file by file. It has
575 `Langlands` modules. No Lean file in it mentions
`SegmentSocleProductIrreducibility`, `SegmentHeadProductIrreducibility`,
`OrderedMultisegmentSocleExistence`, `SquareIntegrableLanglandsClassification`,
`GenericSegmentProductUniqueness`, socle exhaustion, special heads, quotient
coverage or tempered block uniqueness. The only exception is that this
module's own target statement names `TwoBlockProductReversalFactors`. No
paired Markdown file in it cites any excluded task ID as an input. The one
mention is the Independence section of the irreducible-case statement, which
lists the same exclusions for its own proof. The `Classification` modules in
the closure are `Supercuspidal`, `SupercuspidalTwist`,
`SupercuspidalSupport`, `SupercuspidalContragredientStatement`,
`SupercuspidalContragredientAux`, `ConstituentRelations` and `Segments`. The
last two contain only definitions, and basic lemmas about those definitions
(transport along equivalences, twists, linkage symmetry). The others are
`IrreducibleProductEmbedding` and its statement,
`NormalizedProductFiniteLengthStatement`,
`IrreducibleProductFiniteLengthProof` and the two irreducible-case modules.
None of these modules contains an excluded result: the segment and
multisegment conclusions, the adjacent commutation tasks, socle exhaustion,
segment analytic classification, special-head exhaustion and existence,
quotient coverage, tempered block uniqueness, the square-integrable Langlands
classification, square-integrable and regular exhaustion, and generic segment
product uniqueness.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ÉNS 13 (1980), Theorem 1.9,
printed p.174 (literature ID `zelevinsky-1980-induced-ii`). Zelevinsky proves
the finite-length statement directly, by the involution argument; in that
argument only Lemma (b) is reduced to irreducible representations. Here the
division of labour is different. The irreducible case of the theorem is a
separate input, and this module supplies the passage to finite length. That
passage is the standard additivity of composition factors along filtrations,
from exactness of induction. The Lean proof does it with actual filtrations and
graded refinement, not with a Grothendieck group.
