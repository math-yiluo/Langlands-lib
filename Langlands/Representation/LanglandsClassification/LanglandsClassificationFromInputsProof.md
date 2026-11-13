# The Langlands classification from its remaining inputs: proof

Author: Worker 5295. Module
`Langlands.Representation.LanglandsClassification.LanglandsClassificationFromInputsProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module proves one theorem,

`langlandsClassificationFromInputs : LanglandsClassificationFromInputsStatement.{u, v}`.

The statement is the implication
`LeviSecondAdjointnessStatement.{u, v} → LeviInductionFiniteLengthStatement.{u, v} →
RationalPointsIrreducibleAdmissibleStatement.{u, v} → LeviJacquetFiniteLengthStatement.{u, v} →
LanglandsClassificationStatement.{u, v}`. See `LanglandsClassificationFromInputsStatement.md`
for the premises and the source (Renard, VII.4.2, printed pp.243–246 / PDF pp.249–252).

This is a conditional result. It does not prove `LanglandsClassificationStatement` itself:
the four premises are still open. They are the targets of Task 4834 (second adjointness),
Task 4950 (both finite-length statements) and Task 3838 (irreducible implies admissible).

## The proof

The theorem takes the four premises `hAdj`, `hFin`, `hIrr` and `hFL` and returns the
conjunction of parts (i), (ii) and (iii). It combines published reductions and published
proofs. It adds no new mathematics.

- **Part (i)**, `LanglandsQuotientUniqueStatement`, is
  `langlandsQuotientUnique_of_inputs hAdj hFin oppositeIdentitySupport langlandsTripletOppositeKernel`.
  The reduction (module `LanglandsQuotientUniqueReduction`) applies second adjointness to
  `P` and the opposite parabolic `oppositeLeviParabolic`. It uses finite length of
  `i_P^G(σ ⊗ ψ)` to get an irreducible quotient. The VII.4.1 Lemma
  (`langlandsTripletOppositeKernel`, module `LanglandsTripletRegularityProof`) and the identity
  support of the opposite intertwining space (`oppositeIdentitySupport`, module
  `OppositeIdentitySupportProof`) then show that all irreducible quotients have the same
  kernel.
- **Part (ii)**, `LanglandsQuotientInjectiveStatement`, is
  `langlandsQuotientInjective_of_secondAdjointness hAdj` (module
  `LanglandsQuotientMutualRigidityProof`, by Worker 63). That module proves the mutual rigidity
  of two Langlands triplets with a common irreducible quotient, and derives part (ii) from it
  with second adjointness and the VII.4.1 Lemma.
- **Part (iii)**, `LanglandsQuotientExhaustiveStatement`, is
  `langlandsQuotientExhaustive_of_selectedUnitaryUntwist hSel hAdj` (module
  `OppositeJacquetExhaustionReduction`). Here `hSel : OppositeJacquetUntwistSelectionStatement`
  is
  `oppositeJacquetUntwistSelection_of_inputs langlandsCombinatorialDecomposition hIrr hFL oppositeStandardExponentRestriction oppositeUntwistTemperedCriterion`
  (module `OppositeJacquetUntwistSelectionReduction`). That reduction carries out Renard's
  maximal-positive-part argument. It uses admissibility of the irreducible `π` (`hIrr`) and
  finite length of its Jacquet modules (`hFL`) to choose an opposite standard exponent with
  maximal positive part. It then chooses an irreducible subrepresentation `ρ` of the opposite
  Jacquet module `r(π)` on which the split component acts by that exponent, and forms the
  untwist `σ = ρ ⊗ ψ⁻¹`. Here `ψ` is the positive unramified character given by the real part
  of the exponent. Since `σ ⊗ ψ ≅ ρ`, the twist `σ ⊗ ψ` embeds into `r(π)` (the structure
  `UnitaryUntwist` of module `OppositeJacquetUntwist`). Langlands' combinatorial lemma V.3.18
  (`Langlands.GroupScheme.langlandsCombinatorialDecomposition`, module
  `LanglandsDecompositionProof`) and restriction of exponents to a larger standard Levi
  (`oppositeStandardExponentRestriction`, module `OppositeStandardExponentRestrictionProof`) give
  the chamber condition. The temperedness criterion (`oppositeUntwistTemperedCriterion`, module
  `OppositeUntwistTemperedCriterion`, by Worker 63) shows that the untwist `σ` is tempered.
  Second adjointness turns the embedding of `σ ⊗ ψ` into `r(π)` into a nonzero map from
  `i_P^G(σ ⊗ ψ)` to `π`, which is surjective because `π` is irreducible.

## Universes

Every component is used at the universes `u, v` of the statement. Second adjointness is
stated with carriers in `max u v` inside `LeviSecondAdjointnessStatement.{u, v}`, and the three
reductions consume it at those universes.

## Axioms

The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
