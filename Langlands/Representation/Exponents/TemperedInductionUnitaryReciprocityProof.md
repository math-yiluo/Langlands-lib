# Proof of tempered Frobenius reciprocity through the unitary Jacquet part

Author: Worker 837, task `71b5958c-b2a2-4a70-a4f0-537ed8d5a152`. Module
`Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The theorem `temperedInductionUnitaryReciprocity` proves the published statement
`TemperedInductionUnitaryReciprocityStatement.{u, v, w}` (module
`Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityStatement`). This is
the Proposition of Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, VII.2.4, printed p.229 / PDF p.235 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). For tempered `π` of
`G(F)` and tempered `σ` of `M(F)`, it gives a linear bijection
`Hom_G(π, i_P^G σ) ≃ Hom_M((r_P^G π)_0, σ)`. This bijection sends `F` to the map whose
value at an element of the unitary part with Jacquet class `[x]` is `(F x)(1)`. The
field universe `u` and the carrier universes `v` of `σ` and `w` of `π` stay independent.

## The proof

The proof is a single term. It applies the published conditional assembly
`temperedInductionUnitaryReciprocity_of` (module
`Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityReduction`) to two
published proofs:

- `leviFrobeniusReciprocity.{u, v, w}`, the proof of `LeviFrobeniusReciprocityStatement`.
  This is the adjunction of Renard VI.1.2, as the explicit bijection
  `Hom_G(π, i_P^G σ) ≃ Hom_M(r_P^G π, σ)` with `F ↦ ([x] ↦ (F x)(1))`.
- `temperedJacquetUnitaryRestriction.{u, max v w}`, the proof of
  `TemperedJacquetUnitaryRestrictionStatement` at carrier universe `max v w`. For tempered
  `π` and `σ` in one carrier universe, precomposition with the inclusion
  `leviUnitaryJacquetModuleι` is a bijection `(r_P^G π ⟶ σ) → ((r_P^G π)_0 ⟶ σ)`.

The assembly lifts `π` and `σ` to the common carrier universe `max v w` with
`SmoothRep.universeLift`. It shows that the lifts are tempered and that restriction to the
unitary part is bijective for the lifts. It then transports this bijectivity back to `π`
and `σ` along the published universe-lift and Jacquet equivalences. The required
equivalence is the Frobenius bijection followed by this restriction bijection. The
Markdown of the reduction module gives the details in its section "Proof of the
conditional assembly".

## Hypotheses

The theorem keeps every quantifier and datum of the target. It adds no hypothesis to the
target. The two proofs it uses prove their statements outright, and the assembly uses
nothing beyond those statements. Renard's argument needs unimodularity of the radical
`N(F)` for Frobenius reciprocity and complementarity of the unitary and nonunitary
Jacquet parts for the restriction. The two cited proofs derive these facts; they are not
assumptions here. No standardness, finite length, irreducibility, central character,
presentation existence or Jacquet admissibility premise is added.

## Relation to the source

Renard's proof reads: "Ce résultat est la conjonction de la réciprocité de Frobenius VI.1.1
et du lemme III.1.10." ("This result is the conjunction of Frobenius reciprocity VI.1.1
and Lemma III.1.10.") The proof here follows this route. The Frobenius step is
`leviFrobeniusReciprocity`, the normalized adjunction of VI.1.2, which is the
normalized form of the Frobenius reciprocity theorem of VI.1.1 that Renard cites. The Lemma III.1.10 step, that maps to a tempered `σ` vanish on
the nonunitary part, is `temperedJacquetUnitaryRestriction`. The only addition is the
carrier-universe transport in the reduction module. It is needed because the Library
states the restriction step for a single carrier universe.
