# Flatness of the normalization over a Dedekind base

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizationFlat`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `A` be a Dedekind domain and `q : Z ⟶ Spec A` flat, where `Z` can be normalized (its quasi-compact opens have finitely many irreducible components, hypothesis `hZ`).

- `flat_normalization_comp_of_isDedekindDomain`: the normalization morphism of `Z` followed by `q` is flat.
- `flat_normalization_pullback_snd_of_isDedekindDomain`: for `f : X ⟶ Spec A` flat and `g : Spec B ⟶ Spec A` with `B` Dedekind, if every quasi-compact open of the pullback of `X` along `g` has finitely many irreducible components (`hZ`), the normalization of that pullback followed by the projection to `Spec B` is flat. Here `A` is an arbitrary ring.

The proof uses the library's criterion `flat_of_forall_genericPoint_map_eq`: the normalization is reduced, and its generic points map to generic points of `Z`, which the flat `q` sends to the generic point of `Spec A`.

These results serve the reduced fibre theorem (Tag 09IL). The file also cites Tags 0AUW and 035N.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreNormalizationFlat.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
