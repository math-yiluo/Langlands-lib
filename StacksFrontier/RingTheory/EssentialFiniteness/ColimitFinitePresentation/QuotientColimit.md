# Descending polynomial relations through a filtered colimit

Module `StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation.QuotientColimit`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file descends the finite presentation of an algebra to one stage of a directed system. It constructs the polynomial quotients over the resulting tail and proves that their direct limit recovers the given algebra.

## Descent and quotient systems

- `Descent.cofinalColimit` starts with a directed system of commutative local rings and an isomorphism of its direct limit with a local ring `R`, with local stage maps to `R`. Restricting to the indices above `lam0` preserves the direct limit, the structural maps into `R`, and their locality.
- `Descent.descendRelations` assumes that the local ring `R` is a directed colimit of local rings, `T` is finitely presented over `R`, and the local ring `S` is a localization of `T` compatibly with the algebra tower. It finds a prime `q` with `S` the localization of `T` at `q`. It also gives a stage `lam0` and finite polynomial relations over that stage whose images present `T` as an `R`-algebra.
- From a finite list of relations at an index below every stage, `Descent.Tobj` forms `Tᵢ` by quotienting the polynomial ring over `Rᵢ` by the transported relations. `Descent.fTmap` transports coefficients and keeps the polynomial variables fixed. Given coherent base transitions `hRdir` and a recovery presentation `hpres` of the finitely presented algebra `T`, `Descent.colimQuotient` gives `colim Tᵢ ≃+* T` with compatible structural maps over the base. Its conclusion identifies the transitions with `Descent.fTmap`.

The proof contracts the maximal ideal of `S` and lifts the finitely many relation coefficients to a common stage by directedness. For injectivity of the quotient-colimit map, the proof lifts an expression in the relation ideal and passes to a later stage where the coefficient equalities hold.

The quotient construction uses finite lists of variables and relations and a least index `lam0`. The rings and indices live in a single universe. The colimit proved for these stages is the colimit of the quotients before localization.

## References

The file's comments name Tag 00QT as the source of the base system: the presentation of `R` as a filtered colimit of local rings that `Descent.cofinalColimit` and `Descent.descendRelations` take as input. The table of references below cites EGA IV 1.8.4.2, 8.1.1, and 5.13.1, and SGA 3 VIB 10.0.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 1.8.4.2 | `descendRelations` | Local base, special case |
| EGA | IV 8.1.1 | `descendRelations` | special case |
| SGA | 3 VIB 10.0 | `descendRelations` | (ii), special case |
| EGA | IV 5.13.1 | `colimQuotient` | Clause (i), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/EssentialFiniteness/ColimitFinitePresentation/QuotientColimit.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
