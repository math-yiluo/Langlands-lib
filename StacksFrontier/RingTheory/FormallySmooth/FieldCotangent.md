# The cotangent criterion for formal smoothness of a field

Module `StacksFrontier.RingTheory.FormallySmooth.FieldCotangent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a field viewed as an algebra over a commutative ring, formal smoothness is equivalent to vanishing of first cotangent homology.

`Algebra.formallySmooth_iff_subsingleton_h1Cotangent` states that a field K with an R-algebra structure is formally smooth over R exactly when `Algebra.H1Cotangent R K` is a subsingleton. It restates `Stacks.FormallySmooth.CotangentVanishing.solution`.

The proof applies the presentation criterion to the canonical polynomial presentation of K and uses that Ω(K/R) is a vector space over K, hence projective. The result allows an arbitrary commutative base ring R, extending the field-base case of Tag 031Z.

Stacks Project, Tag 031Z and Tag 031J.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [031Z](https://stacks.math.columbia.edu/tag/031Z) | `Algebra.formallySmooth_iff_subsingleton_h1Cotangent` | Stated for a field `K` over an arbitrary commutative base ring `R`; the source's base field `k` is the case `R := k`, and no hypothesis on the base is used. `H_1(L_{K/k}) = 0` is `Subsingleton (Algebra.H1Cotangent R K)`. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/FieldCotangent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
