# Relative dimension at a prime

Module `StacksFrontier.RingTheory.RelativeDimension.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A commutative R-algebra S has a relative dimension at each prime 𝔮 of S.

`Algebra.relativeDimensionAt` takes the topological fibre of Spec S → Spec R over the contraction of 𝔮. It applies the library’s `stacksTopologicalKrullDimAt` to 𝔮 in this subspace, taking the infimum of the dimensions of its open neighbourhoods there. The subspace is homeomorphic to the spectrum of the corresponding residue-field tensor product.

The definition applies to arbitrary commutative algebras, extending the finite-type setting of the tagged definition. Values lie in `WithBot ℕ∞`, which includes −∞ and +∞; the value at a prime is at least zero. The docstrings and the tag note write `topologicalKrullDimAt` for the dimension at a point, and the module docstring also defines a global relative dimension, a supremum over Spec S, that the file does not contain.

Stacks Project Tag 00QD for relative dimension and Tag 0055 (4) for dimension at a point. EGA IV, 17.10.1, in the affine case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00QD](https://stacks.math.columbia.edu/tag/00QD) | `relativeDimensionAt` | The fibre `Spec (S ⊗_R κ(𝔭))` is the homeomorphic subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, in which the source's point `q̄` is `𝔮` itself, and `𝔭 = R ∩ 𝔮` is not an argument; `dim_q̄` is `topologicalKrullDimAt`. The source's finite type hypothesis is unused by the definition and is left to the lemmas. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.10.1 | `relativeDimensionAt` | affine case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RelativeDimension/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `Algebra.relativeDimension`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
