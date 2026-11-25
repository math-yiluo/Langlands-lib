# Finite integral closure in reduced algebras

Module `StacksFrontier.RingTheory.Nagata.IntegralClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The integral closure of a Nagata ring in a reduced algebra essentially of finite type is finite over the base. The proof reduces the ambient algebra to finitely many fields and applies the Japanese property of prime quotients of the base.

`IsIntegralClosure.finite_of_essFiniteType_of_isReduced`, proved by `Stacks.Nagata.IntegralClosureFinite.solution`, gives `Module.Finite R A` for any `A` satisfying `IsIntegralClosure A R S`, with a compatible tower `R → A → S`. It assumes `Algebra.EssFiniteType R S` and `IsReduced S`. The Nagata hypothesis is given as `IsNoetherianRing R` and a hypothesis `hR` that every prime quotient of `R` is Japanese.

Since `S` is Noetherian and reduced, it embeds into the finite product of the fraction fields of its minimal-prime quotients. In each field `K` of this product the structure map factors through the quotient of `R` by its kernel. The relative algebraic closure of the quotient's fraction field in `K` is finite and contains all the elements integral over `R`. The Japanese hypothesis yields a finite module there, and the integral closure in `S` embeds into the product of these finite modules. The private helpers implement change of ambient ring, descent through a finite base extension, and the product argument.

The theorem puts `R` and `S` in the same universe so the Japanese hypothesis can be used on the residue field extensions. The integral closure model `A` can live in a separate universe. Reducedness is needed for the minimal-prime embedding.

References are Tag 03GH, Tag 037J for finiteness of the relative algebraic closure, Tag 02LX and Tag 00EU for the minimal-prime reduction, and EGA II 6.3.10 for a more general statement.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [03GH](https://stacks.math.columbia.edu/tag/03GH) | `IsIntegralClosure.finite_of_essFiniteType_of_isReduced` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.10 | `solution` | special case |
| EGA | II 6.3.10 | `IsIntegralClosure.finite_of_essFiniteType_of_isReduced` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/IntegralClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
