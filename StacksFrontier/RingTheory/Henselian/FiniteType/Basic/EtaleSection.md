# Henselian sections of étale algebras at residue-rational points

Module `StacksFrontier.RingTheory.Henselian.FiniteType.Basic.EtaleSection`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file gives a local ingredient for splitting a finite type algebra over a henselian local ring: a retraction of an étale algebra at a residue-rational point of its closed fibre.

## Main results

- `henselian_etale_residue_point_section` takes a henselian local ring R with maximal ideal 𝔪 and an étale R-algebra R′ with a prime P over 𝔪. If the induced residue-field map is bijective, it gives an R-algebra retraction σ from R′ to R such that each element of R′ and the image of its σ-value agree modulo P.

For the retraction, the proof passes to a standard étale chart at P, where `henselian_etale_standardChart_hasMap` lifts a simple root and keeps its localization denominator invertible; the section sends the chart coordinate to that root.

The section statement places R and R′ in the same universe. The compatibility lemma `henselian_etale_section_residue_compat` takes `hpin`, the equality identifying the lifted root's residue with the chart coordinate at P. The chart lemma supplies this equality. The retraction gives the residue-rational étale case of the splitting condition in Tag 04GG. The module docstring also announces a product decomposition attached to an idempotent and the finiteness of the quasi-finite primes over the maximal ideal; neither is in the file.

## References

Tag 04GG. See EGA IV 18.5.11, EGA IV 18.5.17, and EGA IV 18.8.1. See also SGA 1 III 3.3, SGA 3 VIB 5.6.1, SGA 3 X 4.5, SGA 3 XI 1.11, and SGA 4 XII 6.13.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 X 4.5 | `henselian_etale_standardChart_hasMap` | special case |
| SGA | 3 XI 1.11 | `henselian_etale_standardChart_hasMap` | special case |
| EGA | IV 18.5.11 | `henselian_etale_residue_point_section` | special case |
| EGA | IV 18.5.17 | `henselian_etale_residue_point_section` | affine étale morphisms |
| EGA | IV 18.8.1 | `henselian_etale_residue_point_section` | (a)⇒(c), special case |
| SGA | 1 III 3.3 | `henselian_etale_residue_point_section` | special case |
| SGA | 3 VIB 5.6.1 | `henselian_etale_residue_point_section` | special case |
| SGA | 3 X 4.5 | `henselian_etale_residue_point_section` | special case |
| SGA | 4 XII 6.13 | `henselian_etale_residue_point_section` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Henselian/FiniteType/Basic/EtaleSection.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 5 are kept. The 5 left out are not needed by the results for which the extract is made: `closedFibre_localization_isArtinian`, `idem_algEquiv_prod`, `map_maximalIdeal_le_of_liesOver`, `not_qf_over_maximal_of_algEquiv`, `qf_primesOver_maximal_finite`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 9 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
