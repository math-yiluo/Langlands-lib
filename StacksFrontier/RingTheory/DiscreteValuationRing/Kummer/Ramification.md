# Ramification of extensions obtained by adjoining a root of a uniformizer

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Kummer.Ramification`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring with fraction field K and uniformizer π. Write A′ = A[X]/(Xⁿ − π), K₁ = K[X]/(Xⁿ − π), and A₁ for the integral closure of A in K₁. Write π′ for the adjoined root.

- For n ≥ 1, `residueA'` sends π′ to zero and constants to their residues in the residue field of A. It is surjective, and `ker_residueA'` identifies its kernel with (π′).
- For n ≥ 2, `isDiscreteValuationRing_A'` shows that A′ is a discrete valuation ring if it is a domain. `isDiscreteValuationRing_A1` gives the same conclusion for A₁ using the canonical equivalence with A′. `irreducible_piRoot` supplies the uniformizer π′ of A₁.
- `exists_ramificationIdx_eq` gives a unique maximal ideal over the maximal ideal of A with ramification index n. `isTotallyRamified_K1` proves total ramification in the library's sense, with inertia degree one at that ideal, in all residue characteristics.
- `isSeparable_K1` gives separability when the residue characteristic is zero or coprime to n.

Finiteness and integrality force every maximal ideal of A′ to contain π′, and the residue map makes (π′) maximal. The equation (π′)ⁿ = π computes the index. The ramification–inertia sum and the degree n give inertia degree one, while separability follows from that of Xⁿ − π.

The statements for A₁ being a discrete valuation ring and for total ramification take a `Fact` instance of irreducibility over K. The discrete valuation ring, index and total ramification assertions are Tag 09EV (3)–(5). The module docstring also announces tame ramification, Tag 09EV (6), which the file does not contain.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09EV](https://stacks.math.columbia.edu/tag/09EV) | `isDiscreteValuationRing_A1` | (3) |
| [09EV](https://stacks.math.columbia.edu/tag/09EV) | `exists_ramificationIdx_eq` | (4) |
| [09EV](https://stacks.math.columbia.edu/tag/09EV) | `isTotallyRamified_K1` | (5) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Kummer/Ramification.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 19 declarations of the source file 18 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.KummerExtension.isTamelyRamified_K1`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
