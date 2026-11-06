# Renard VII.1.3 from its remaining inputs

Author: Worker 1507. Module
`Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityFromInputsStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The module contains one `Prop`-valued definition,
`MaximalLeviSupercuspidalReducibilityFromInputsStatement.{u, v}`. It is neither assumed nor
proved here.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VII.1.3, Theorem and its proof (printed pp.224–226 / PDF pp.230–232). The
registered source ID is `renard-2026-representations-groupes-reductifs-padiques`. Its
conclusion is the published `MaximalLeviSupercuspidalReducibilityStatement`; see
`MaximalLeviSupercuspidalReducibilityStatement.md`.

## The statement

`MaximalLeviSupercuspidalReducibilityFromInputsStatement.{u, v}` is an iterated implication.
Its conclusion is `MaximalLeviSupercuspidalReducibilityStatement.{u, v}`, which covers
fields `k : Type u` and representations of `M(F)` with carriers in `Type v`. Its premises
are eleven published propositions, in this order:

1. `ParabolicDynamicStatement.{u}` (Milne, Theorem 25.1): a closed subgroup of a connected
   reductive group is parabolic if and only if it is the dynamic `P(χ)` of a cocharacter.
2. `RationalPointsIrreducibleAdmissibleStatement.{u, v}` (Renard VI.2.2): irreducible smooth
   representations of `G(F)` with carriers in `Type v` are admissible.
3. `RationalPointsIrreducibleAdmissibleStatement.{u, max u v}`: the same for carriers in
   `Type (max u v)`, the universe of the induced representations `i_P^G ρ`.
4. `ArbitraryParabolicQuotientCompactStatement.{u}`: `P(F) \ G(F)` is compact for every
   represented parabolic `P`.
5. `RationalPointFamily.RationalReductiveUnimodularityStatement.{u}`: rational points of
   connected reductive groups are unimodular. This statement takes the next premise as an
   argument.
6. `StandardCocharacterStatement.{u}`: standard cocharacters exist, and standard subgroups
   are the corresponding dynamic subgroups.
7. `ParabolicRootPresentationExistenceStatement.{u}` (Renard V.3.14–V.3.15): every
   parabolic, rational Levi and split component of the Levi admit a compatible root
   presentation.
8. `SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v}` (Renard VI.2.1 and
   IV.3.2): an irreducible supercuspidal representation with a unitary central character is
   unitarizable.
9. `MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v}` (Renard III.2.5 and
   VI.5.3): for a maximal parabolic and an irreducible supercuspidal `ρ`, every endomorphism
   of `i_P^G ρ` is a scalar, or a Weyl element normalizes `M` and conjugates `ρ` to itself.
10. `MaximalLeviSupercuspidalInductionHomStatement.{u, v}` (Renard III.2.5 and VI.5.3): a
    nonzero morphism `i_P^G τ' → i_P^G τ` between inductions of irreducible supercuspidals
    forces `τ' ≅ τ`, or a Weyl element normalizing `M` that conjugates `τ` to `τ'`.
11. `MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v}` (the Casselman-criterion
    step of VII.1.3, with VII.1.2, VI.5.4 and IV.3.2): if `ρ` has no unitary central
    character and `i_P^G ρ` is reducible with a unitary central character, then `i_P^G ρ`
    has an irreducible unitarizable subrepresentation or quotient.

Premises 8 to 11 are stated in the published module `MaximalLeviReducibilityUnitaryInputs`.
Their exact formulations and literature locators are in
`MaximalLeviReducibilityUnitaryInputs.md`.

## Why these premises

They are the published results that Renard's proof of VII.1.3 uses and that are not yet
proved in the Library. In that proof:

- Premise 1 places the center of `G(F)` inside `P(F)`. This gives the unramified twist
  that makes the central character of `i_P^G ρ` unitary (the first paragraph of the
  proof, through VI.8.5; see `MaximalLeviReducibilityReductionStatements.md`).
- Premises 4 to 7 give the properties of normalized induction the proof uses.
  Induction preserves admissibility (III.2.3) and unitarizability (IV.2.3).
  The hermitian dual of `i_P^G (σ ⊗ χ)` is `i_P^G (σ ⊗ conj(χ)⁻¹)` (IV.2.1.2).
  Premise 7 enters through the modular character of `P(F)` (V.5.4). The input statements
  `LeviInductionAdmissibleStatement`, `LeviInductionUnitarizableStatement` and
  `LeviInductionHermitianDualityStatement` of `MaximalLeviReducibilityUnitaryInputs` are
  not premises here, because they follow from premises 4 to 7.
  `LeviInductionNontrivialStatement` is not a premise either, because it follows from
  continuity of the Levi projection alone.
- Premises 2, 3 and 8 to 11 are the remaining steps of the unitary case (Chapters IV, VI
  and the Casselman criterion).

## Faithfulness notes

- **No change to the target.** The conclusion is the published target statement at the
  same universes `u, v`. Every premise is a published proposition used at its own
  universes. No premise mentions the specific `G`, `P` or `ρ` of the target, so this is a
  plain implication between closed statements.
- **Universes.** Premise 3 is premise 2 at the carrier universe `max u v`. This is where
  `leviInductionFunctor` takes values, and the proof applies admissibility to irreducible
  constituents of `i_P^G ρ`.
- **Strength.** All premises are results of the literature (or, for 9–11, statements derived
  from Renard's proof and published with their own provenance). None of them is the
  target or contains it.

## Provenance

Derived. The statement records which published inputs the proof of Renard VII.1.3 needs in
the represented-parabolic interface. It lets the conditional proof be reviewed and
published separately from the proofs of those inputs. Combining it with proofs of the
eleven premises gives the target.
