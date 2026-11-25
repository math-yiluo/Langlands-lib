# Idempotents in the closed fibre of a finite algebra

Module `StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ArtinianIdempotents`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The closed fibre of a module-finite algebra over a local ring is Artinian. Its local factors give idempotents that, over a henselian base, can be lifted to isolate individual points of the fibre.

## Main results

- `closedFibre_isArtinian'` proves that A/𝔪A is Artinian for a module-finite algebra A over a local ring R with maximal ideal 𝔪. The quotient is finite-dimensional over R/𝔪.
- `artinian_coi_local` gives a finite family eᵢ of pairwise orthogonal idempotents summing to 1 in any commutative Artinian ring T. Each factor T/(1 − eᵢ) is local.
- `reduction_of_isolating_idem` assumes that R is henselian and A is module-finite. For a prime 𝔮 of A over 𝔪, it constructs an idempotent outside 𝔮 and in every other prime over 𝔪. Its image in the closed fibre is the primitive idempotent supported at 𝔮.

The Artinian decomposition lifts the coordinate idempotents of the product of residue fields through the nilpotent Jacobson radical. The isolating idempotent is obtained over a pointed étale neighbourhood and then transported back along its residue-compatible henselian section.

The file provides the closed-fibre and single-point lifting steps for the finite-algebra decomposition condition of Tag 04GG.

In `closedFibre_isArtinian'` and `reduction_of_isolating_idem`, R is in `Type u` and A in `Type (max u v)`, so the universe of A must be at least that of R.

## References

Tag 04GG and Tag 00UJ. The Artinian results are cited as special cases of EGA IV 2.5.8.8 and EGA I 6.2.2, and the local-factor result gives part of SGA 3 VIIB 0.1.1.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.5.8.8 | `closedFibre_isArtinian'` | special case |
| EGA | I 6.2.2 | `artinian_coi_local` | special case |
| SGA | 3 VIIB 0.1.1 | `artinian_coi_local` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Henselian/FiniteType/Basic/ArtinianIdempotents.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
