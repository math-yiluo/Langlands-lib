# Divisorial quotients of a Noetherian normal domain

Module `StacksFrontier.RingTheory.Serre.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a Noetherian integrally closed domain R with fraction field K, `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` describes the height-one primes of R through its divisorial quotients. For nonzero a in R or nonzero x in K, the associated primes of R/aR or R/(R ∩ xR), respectively, are minimal among associated primes and have height one in R. The intersection of the height-one localizations in K equals the image of R.

Integral closedness controls the elements stabilizing a nonzero ideal. The principal ideal theorem supplies the height bound, and clearing denominators reduces the fractional case to the principal case.

The module docstring also defines the conditions (Rₖ) and (Sₖ) and a fibre ring, and states the (S₁) criterion for embedded associated primes (Stacks 031P and 031Q); none of these is in the file, whose section on (S₁) is empty.

## References

Tag 031T gives the normal-domain results. The EGA references are EGA 0 23.2.9 and EGA IV 7.8.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [031T](https://stacks.math.columbia.edu/tag/031T) | `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` | A normal domain is `IsDomain` plus `IsIntegrallyClosed`, as in Definition 0309; \   having no embedded primes is spelled with `Minimal`, as in tags 02M6 and 031Q; item (2) is the \   equality `⨅ 𝔭, R_𝔭 = ⊥` of `R`-subalgebras of `K`, as in \   `IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot`; and `R ∩ xR` is the pullback of \   `xR ⊆ K` along `Algebra.linearMap R K`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.2.9 | `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` | A normal (A = A') |
| EGA | IV 7.8.3 | `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` | (viii), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Serre/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 27 declarations of the source file 11 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
