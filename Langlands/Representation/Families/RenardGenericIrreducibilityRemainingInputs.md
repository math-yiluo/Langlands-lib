# Renard VI.8.5 from its three remaining inputs

This is a supporting module for Renard VI.8.5. It does not prove the closed target
`GenericInducedIrreducibilityStatement`.

Source: Renard, *Représentations des groupes réductifs p-adiques*, French version of
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`), VI.8.5 (printed
pp.193–194, PDF pp.199–200). The mathematical argument is in the published reduction
`genericInducedIrreducibility_of_statements`
(`Langlands/Representation/Families/RenardGenericIrreducibilityReduction.lean`),
whose Markdown describes it. This module adds no new mathematics; it only discharges
published inputs of that reduction.

## Main theorem

`Langlands.Renard.AlgebraicFamily.genericInducedIrreducibility_of_remainingStatements`, at
independent universes `u` (field) and `v` (representation of `M(F)`), takes exactly three
hypotheses and concludes `GenericInducedIrreducibilityStatement.{u, v}`:

1. `hOpen : InducedIrreducibilityOpenStatement.{u, v}`, Renard VI.8.4: if `i_P^G(ρ ⊗ ψ₀)` is
   irreducible for one unramified `ψ₀`, it is irreducible on a principal Zariski open set
   containing `ψ₀`;
2. `hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v}`, Jacquet's theorem
   (Renard VI.2.2): irreducible smooth representations of the rational points of a connected
   reductive group are admissible;
3. `hSU : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v}`, Renard VI.2.1
   with IV.3.2: an irreducible supercuspidal representation with unitary central character
   is unitarizable.

These are inputs 1–3 of `genericInducedIrreducibility_of_statements`, unchanged. Each is a
published statement, and the Library proves none of the three unconditionally. Once all
three are proved, applying this theorem to their proofs proves the closed target.

## Packaged form

`GenericInducedIrreducibilityRemainingInputs.{u, v}` is a proposition structure with three
fields, `inducedIrreducibilityOpen`, `irreducibleAdmissible` and `supercuspidalUnitarizable`.
They are the three propositions above, in the same order and at the same universes, and
they coincide with the first three fields of the published
`GenericInducedIrreducibilityInputs.{u, v}` (same field names). The structure is an internal
packaging device, following the published `GenericInducedIrreducibilityInputs`; it has no
separate literature counterpart.

- `genericInducedIrreducibilityInputs_of_remainingInputs` builds
  `GenericInducedIrreducibilityInputs.{u, v}` from it: the first three fields are copied, and
  the other five are the proofs listed below.
- `genericInducedIrreducibility_of_remainingInputs` proves
  `GenericInducedIrreducibilityStatement.{u, v}` from it, by passing its fields to
  `genericInducedIrreducibility_of_remainingStatements`.

Nothing in this module proves `GenericInducedIrreducibilityRemainingInputs`.

## Proof

The proof is one application of `genericInducedIrreducibility_of_statements` to the three
hypotheses and to proofs of its inputs 4–8:

4. `LeviInductionAdmissibleStatement.{u, v}` (normalized induction preserves admissibility,
   Renard III.2.3): `leviInductionAdmissible`, from
   `Langlands/Representation/Exponents/LeviInductionUnitarityProof.lean`;
5. `LeviInductionUnitarizableStatement.{u, v}` (normalized induction preserves
   unitarizability, Renard IV.2.3): `leviInductionUnitarizable`, same module;
6. `LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v}` (Renard VI.5.3(iii)):
   the published `leviJacquetInductionSupercuspidalFiltration`
   (`Langlands/Representation/Exponents/LeviJacquetInductionSupercuspidalFiltrationProof.lean`);
7. `LeviNormalizerFiniteQuotientStatement.{u}` (`N_G(M)(F)/M(F)` is finite): the published
   `leviNormalizerFiniteQuotient`
   (`Langlands/Representation/Exponents/LeviNormalizerQuotientProof.lean`);
8. `LeviNormalizerNormFixingStatement.{u}` (a normalizing element preserving all
   rational-character norms on the centre of `M(F)` lies in `M(F)`): the published
   `leviNormalizerNormFixing`, same module.

All three namespaces are `Langlands.Aubert.General.RepresentedParabolic`. The only axioms
used are `propext`, `Classical.choice` and `Quot.sound`.
