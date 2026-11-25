# Primes over a maximal ideal of a one-dimensional Noetherian domain

Module `StacksFrontier.RingTheory.Ideal.Over.HeightOne`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file shows that a domain whose fraction field is finite over that of a one-dimensional Noetherian domain has finite fibres, made of maximal ideals, over the maximal ideals of the base.

## Main results

- `Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient` takes a Noetherian domain R of dimension at most one, a domain S over R, and compatible fraction fields K of R and L of S with L finite over K. For any maximal ideal m of R, the primes n of S over m are maximal and finite in number. The quotients S/n and the fibre ring S/mS are finite-dimensional over R/m. The same statement is declared as `Stacks.PrimesOver.KrullAkizuki.solution`, and the theorem is that declaration.

S embeds R-linearly in L, a finite-dimensional K-vector space. For a nonzero x in m the length bound `length_quotient_smul_le_finrank_mul` of `StacksFrontier.RingTheory.KrullAkizuki.IntermediateRingNoetherian` makes S/xS of finite length over R, so its quotient S/mS is a finite R-module; when m = ⊥, R is a field and S is already finite over R. Then S/mS is an Artinian ring with finitely many primes, and each S/n is an Artinian domain, hence a field.

## Scope and references

Tag 031F applies at an arbitrary maximal ideal, including the field case, and allows S of infinite type over R. The fibre can be empty. The length argument uses Tag 00PE. The module docstrings of the file also describe a height-one result for generically finite extensions (Tag 02MA) and finiteness results for residue fields of local homomorphisms; neither is in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [031F](https://stacks.math.columbia.edu/tag/031F) | `isMaximal_and_finite_primesOver_and_module_finite_quotient` | The three assertions of the tag, for an arbitrary maximal ideal `m` of a Noetherian domain with `Ring.KrullDimLE 1` rather than for the maximal ideal of a local ring of dimension one, together with the finite-dimensionality of `S/mS` over `κ(m)` from which the author's proof deduces them. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Ideal/Over/HeightOne.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 7 are kept. The 11 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
