# From a presentation of the reduction to the normalization

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReductionNormalization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Results elsewhere present the reduction of a scheme `W` abstractly, as a closed immersion `ρ : Z ⟶ W` whose kernel is the nilradical, while the comparison of the normalization of `W` with that of its reduction is stated for `W.nilradical.subscheme`. This file connects the two, for the reduced fibre theorem (Tag 09IL).

- `exists_iso_nilradical_subscheme_of_ker_eq_nilradical`: such a `ρ` is isomorphic over `W` to `W.nilradical.subscheme`. Reducedness of `Z` is not assumed.
- `exists_dense_open_smooth_normalization_of_ker_eq_nilradical`: let `q : W ⟶ Spec k` be locally of finite type over a field, with every quasi-compact open of `W` having finitely many irreducible components (hypothesis `hW`). If such a `ρ` has a dense open of `Z` smooth over `k`, the normalization of `W` has a dense open smooth over `k`.

Two closed immersions with the same kernel are isomorphic, by the universal property of closed immersions. The dense smooth open is moved to the reduction, passed to its normalization, and carried back along the comparison of normalizations.

The file also cites Tag 035Q.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreReductionNormalization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
