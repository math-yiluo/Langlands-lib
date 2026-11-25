# Dimension of a quasi-finite algebra over affine space

Module `StacksFrontier.RingTheory.QuasiFinite.AffineSpaceDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A quasi-finite algebra over a polynomial ring in n variables over a field has Krull dimension at most n.

`ringKrullDim_le_natCard_of_quasiFinite_mvPolynomial` takes a field k, a finite index type σ and a commutative `MvPolynomial σ k`-algebra S with `Algebra.QuasiFinite (MvPolynomial σ k) S`. It bounds `ringKrullDim S` by `Nat.card σ`. The statement is proved as `Stacks.QuasiFinite.AffineSpaceDimension.solution`.

The private `ringKrullDim_le_of_quasiFinite` bounds the dimension of any quasi-finite algebra by that of its base. At each prime of the algebra, its height is at most the height of its contraction. Taking the supremum and using the dimension formula for the polynomial ring over k proves the result.

Mathlib’s `Algebra.QuasiFinite` asks for finite-dimensional fibres over residue fields. The Lean formulation of Tag 00QG also covers algebras with noninjective structure maps and algebras that are not of finite type. The variable type must be finite, and the dimension inequality includes the zero algebra with dimension ⊥.

The height bound is Tag 00QF. The comments cite Tag 00OP for the local dimension computation in the source, Tag 00PL for quasi-finiteness, and Tag 00PM for the fibre criterion in finite type.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00QG](https://stacks.math.columbia.edu/tag/00QG) | `ringKrullDim_le_natCard_of_quasiFinite_mvPolynomial` | The source's `k[t_1, …, t_n] ⊂ S` with `S` of finite type over `k` and the map quasi-finite is weakened to `Algebra.QuasiFinite (MvPolynomial σ k) S` with `Finite σ`, which the source's hypotheses imply (tag 00PM); neither finite type nor injectivity is used. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/QuasiFinite/AffineSpaceDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
