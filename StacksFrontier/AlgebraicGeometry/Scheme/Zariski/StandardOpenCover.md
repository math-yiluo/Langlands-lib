# Finite refinements of open covers of a standard open

Module `StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one lemma. Let R be a commutative semiring and `D(f)` a standard open of its prime spectrum. `PrimeSpectrum.exists_finite_basicOpen_refinement` refines an arbitrary open cover of `D(f)` to finitely many standard opens: there are g₁, …, gₙ in R with `D(f)` the union of the `D(gⱼ)` and each `D(gⱼ)` contained in a member of the cover. The proof uses the basis of standard opens and the quasi-compactness of `D(f)`.

The module docstring also describes standard open coverings as a definition, the unit-ideal criterion for covering and a divisibility criterion for containment of standard opens; these are not in the file.

The reference for the lemma is Stacks Project, Tag 01HS. The tables also record Tag 01HS and EGA I 1.3.2 for Mathlib’s criterion equating `D(g) ⊆ D(f)` with invertibility of `f` after localization at `g`.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01HS](https://stacks.math.columbia.edu/tag/01HS) | `exists_finite_basicOpen_refinement` | finite_standard_refinement |
| [01HS](https://stacks.math.columbia.edu/tag/01HS) | `PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit` | invertible_on_smaller_open |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 1.3.2 | `PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit` | (a) ⇔ (f) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Scheme/Zariski/StandardOpenCover.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 1 are kept. The 4 left out are not needed by the results for which the extract is made: `PrimeSpectrum.IsStandardOpenCover`, `PrimeSpectrum.IsStandardOpenCoverOfSpectrum`, `PrimeSpectrum.basicOpen_le_iSup_iff_span_algebraMap_eq_top`, `PrimeSpectrum.exists_pow_eq_mul_of_basicOpen_le`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
