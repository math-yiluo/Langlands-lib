# Exactness of module sheaves on stalks

Module `StacksFrontier.Topology.Sheaves.Modules.Exactness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a sheaf of rings 𝒪 on a topological space X, exactness at the middle term of a short complex of 𝒪-module sheaves can be tested at every point.

`AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor` takes the stalk of the underlying presheaf of abelian groups at x and preserves zero morphisms. `stalkShortComplex` applies it to the two arrows of the complex. The theorem `exact_iff_stalkShortComplex_exact` equates exactness of the original complex with exactness of every such stalk complex.

The proof uses the faithful exact forgetful functor to sheaves of abelian groups and their stalkwise exactness criterion. The stalk complexes are formed in abelian groups. The abelian structure on the module sheaf category comes from Mathlib's `SheafOfModules.instAbelian`.

Tag 01AG covers exactness on stalks and the abelian category instance.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01AG](https://stacks.math.columbia.edu/tag/01AG) | `exact_iff_stalkShortComplex_exact` | exactness on stalks |
| [01AG](https://stacks.math.columbia.edu/tag/01AG) | `SheafOfModules.instAbelian` | the category of sheaves of modules is abelian |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Modules/Exactness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
