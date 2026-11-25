# The reduction of a scheme and reducedness of its normalization

Module `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The reduction of a scheme X can be normalized whenever X can, and the normalization of X is
reduced. Throughout, the normalization of X takes a witness `hX` that every quasi-compact open
has finitely many irreducible components.

- `Scheme.homeomorphNilradicalSubscheme` identifies the space of the reduction
  `X.nilradical.subscheme` with X: the closed immersion of the reduction is a closed embedding,
  and it is surjective because the nilradical ideal sheaf is supported everywhere.
- `finite_irreducibleComponents_reduction` transfers the component finiteness hypothesis
  to the reduction, so that the reduction can itself be normalized.
- `Scheme.isReduced_normalizationScheme` shows that the normalization
  `X.normalizationScheme hX` is a reduced scheme.

The finiteness transfer is topological: a homeomorphism carries irreducible components to
irreducible components. The normalization is reduced because it is formed as a relative
normalization in a coproduct of spectra of fields, which is reduced.

The module docstring also announces the factorization of the normalization morphism through the
reduction and its identification with the normalization of the reduction (Tag 035O); they are
not in this file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/Reduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 6 are kept. The 18 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
