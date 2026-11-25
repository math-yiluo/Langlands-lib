# Descent of N-1 and N-2 along finite extensions

Module `StacksFrontier.RingTheory.Nagata.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that finite normalization (N-1) and finiteness of integral closure in every finite extension of the fraction field (N-2, or Japanese) descend along finite extensions of Noetherian domains.

- `isN1_of_finite_of_isN1` and `isN2_of_finite_of_isN2` descend the corresponding properties, `StacksIsN1` and `IsN2_032k`, from `S` along an injective, module-finite map of domains `R → S` with `R` Noetherian.
- `isN_core` is their common step: for `R` a Noetherian domain, `S` a domain module-finite over `R`, an injective `R`-algebra map `K → L` of fields, and the integral closure of `S` in `L` finite over `S`, the integral closure of `R` in `K` is finite over `R`. `isN2_step` is the N-2 case for one finite extension `L` of the fraction field of `R`.
- `isN1_of_le_fg` shows that over a Noetherian ring an integral closure contained in a finitely generated submodule is a finite module.

For finite extensions, `isN_core` embeds one integral closure into another, which is finite over `R` because it is finite over `S`; Noetherianity of `R` then makes the embedded module finite. In the N-1 case the embedding is the lift `Frac R → Frac S` of the structure map. In the N-2 case the larger field is a maximal-ideal quotient of the tensor product `Frac S ⊗ L`.

The descent theorem uses `IsN2_032k`, which quantifies over extension fields in the domain's universe, so the tensor-product quotient is transported to that universe. The file keeps three module docstrings, on descent from the Laurent polynomial ring, on descent along finite extensions and on the equivalence of N-1 and N-2 in characteristic zero; only the second describes results that the file holds, and a namespace left from the first holds only a variable and comments.

References are Tag 032K (1) and (2).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032K](https://stacks.math.columbia.edu/tag/032K) | `isN1_of_finite_of_isN1` | (1) |
| [032K](https://stacks.math.columbia.edu/tag/032K) | `isN2_of_finite_of_isN2` | (2) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 28 declarations of the source file 6 are kept. The 22 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 4 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
