# Algebraic formal smoothness for an adic target

Module `StacksFrontier.RingTheory.FormallySmooth.Algebraic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Algebraic formal smoothness supplies continuous lifts for maps into discrete square-zero quotients when the target of the original homomorphism has an adic topology.

`RingHom.FormallySmoothTop.of_formallySmooth_of_isAdic` takes a homomorphism φ : R → S of rings with topological ring structures. It assumes `Algebra.FormallySmooth` for the algebra defined by φ and that S carries the topology of an ideal n. The conclusion is the continuous lifting predicate `RingHom.FormallySmoothTop`. This is the implication from algebraic formal smoothness for an adic target in Tag 07EC.

The proof applies algebraic formal smoothness to lift across A → A/J. Continuity into the discrete quotient means the map kills nᵏ for some k ≥ 1. The lift sends nᵏ into J, so it kills n²ᵏ by the square-zero hypothesis and is continuous.

Stacks Project, Tag 07EC. EGA 0 19.3.8 for discrete topologies.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07EC](https://stacks.math.columbia.edu/tag/07EC) | `of_formallySmooth_of_isAdic` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.3.8 | `of_formallySmooth_of_isAdic` | discrete topologies |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/Algebraic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
