# Kernels of surjections onto finitely presented sheaves of modules

Module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a sheaf of rings on a site `(C, J)`. If `F` is a sheaf of `R`-modules of finite presentation and `θ : G ⟶ F` is an epimorphism with `G` of finite type, then `ker θ` is of finite type. An imported file proves this when `F` has a global finite presentation and `G` finitely many global generators; this file handles the passage from the local notions in Mathlib's `IsFinitePresentation` and `IsFiniteType`, whose covering families need not agree. Despite the file's name, it contains nothing about tensor products.

## Main definitions and results

- `presentationOver`, `generatingSectionsOver`: restriction of a presentation, resp. of generating sections, of `M.over V` along `W ⟶ V`, preserving finiteness.
- `generatingSectionsIteratedSlice` and `bindLocalGeneratorsData`: local generators on the members of a covering family glued into local generators of `M`.
- `isFiniteType_of_coversTop`: being of finite type is local on the base.
- `isFiniteType_kernel_over`: over an object carrying both a finite presentation of the target and finite generators of the source, the restricted kernel is of finite type.
- `kernel_isFiniteType_of_epi_from_finiteType` (instance): the statement above.

## Proofs

Intersect the covering sieve where `F` is finitely presented with the one where `G` is finitely generated; on each member, restrict both data and apply the global theorem on the slice site; conclude by locality of finite type.

## Points to watch

- Colimit preservation by the restriction functors (to a slice, to a slice of a slice, along a morphism) is assumed as instance hypotheses, not derived; the file explains that these hold on sites with binary products and pullbacks and also on sites without finite limits.
- `HasSheafify` and `WEqualsLocallyBijective` for abelian groups are required on `J`, on every slice and on every iterated slice.
- The module docstring also announces the case of a finite free source (part (1) of Tag 01BP), which the file does not contain.

## References

Tag 01BP; Tag 082T (the statement for an arbitrary ringed site), Tags 01B4 and 01BD.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01BP](https://stacks.math.columbia.edu/tag/01BP) | `kernel_isFiniteType_of_epi_from_finiteType` | part (2) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactnessSheafify.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 12 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.SheafOfModules.LocalKernel.generatingSectionsIteratedSlice_isFiniteType`, `Stacks.SheafOfModules.LocalKernel.isFiniteType_free`, `Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finite_free`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
