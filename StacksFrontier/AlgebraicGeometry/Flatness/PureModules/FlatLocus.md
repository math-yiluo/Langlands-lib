# Relative flatness at a point under restriction to an open

Module `StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `F`, the file shows that flatness of `F` over `S` at a point, that is, flatness of the stalk `F_x` over the local ring of `S` at `f x`, is unchanged by restriction along an open immersion.

## Definitions and results

- `restrictStalkMap j F w`: for an open immersion `j : W ⟶ X`, the comparison of the stalk at `w` of the restriction of `F` with the stalk of `F` at `j w`. `restrictStalkMap_smul` shows that it is linear over the local ring of `X` at `j w`, which acts on the source through the stalk map of `j`.
- `isFlatOverAt_restrict_iff`: the restriction of `F` along `j` is flat over `S` at `w` (for `j ≫ f`) if and only if `F` is flat over `S` at `j w`.

## Proofs

The comparison of stalks is an isomorphism of abelian groups, from `Scheme.Modules.restrictStalkNatIso`. Its compatibility with scalars is checked on germs (a private lemma computes it on germs), which turns it into a linear equivalence over the local ring of `S` at `f (j w)`, and flatness is transported along it.

## To watch for

- Flatness at a point is the library's `IsFlatOverAt`, stated for the underlying morphism of sheafed spaces.
- The module docstring announces the flat locus of `F` over `S` and the flatness of the restriction of `F` to an open contained in it. The file holds neither.

## References

The file cites Tag 05IK.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Flatness/PureModules/FlatLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 4 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.flatLocus`, `AlgebraicGeometry.isFlatOver_restrict_of_subset_flatLocus`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
