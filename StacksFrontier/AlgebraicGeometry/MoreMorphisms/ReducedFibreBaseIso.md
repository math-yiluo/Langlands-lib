# Changing the base of a normalized base change by an isomorphism

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreBaseIso`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `f : X ⟶ T`, `i : S ⟶ T`, and let `s : S' ⟶ S` be an isomorphism. The base changes of `f` along `s ≫ i` and along `i` differ only by the identification `s` of their bases. The file shows that the normalizations of the two base changes are isomorphic over `s`, and that smoothness at every generic point of every fibre passes from the one to the other. This is a transport step in the reduced fibre theorem (Tag 09IL): its proof produces the final base as an integral closure that is the same subring of a field as the one named in the tag, but a different type, so the conclusion must move along a ring isomorphism of bases.

## Main results

- `isPullback_fst_snd_comp_of_isIso`: when `s` is an isomorphism, `X ×_T S'` (along `s ≫ i`), with second projection followed by `s`, is a pullback of `f` along `i`. It is obtained by pasting with a square whose horizontal arrows are isomorphisms.
- `exists_normalizationScheme_iso_pullback_comp_of_isIso`: given finiteness of irreducible components on quasi-compact opens of both pullbacks (`h₁`, `h₂`), there is an isomorphism of normalizations carrying the structure morphism over `S'`, followed by `s`, to the one over `S`.
- `smoothAt_normalization_pullback_of_isIso_base`: for `j : S' ⟶ T` with `j = s ≫ i`, if the normalization of `X ×_T S'` is smooth over `S'` (`InfinitesimalLifting.SmoothAt`) at every point that is generic in its fibre, then so is the normalization of `X ×_T S` over `S`.
- `mem_genericPoints_asFiber_fiberι`: a generic point of the fibre `f.fiber t` is, read in `X`, a generic point of its own fibre.

## Proofs

The normalizations are compared with `Scheme.exists_normalizationScheme_iso_of_iso`; smoothness and the generic-point condition are moved by `InfinitesimalLifting.smoothAt_iso_hom_iff` and `mem_genericPoints_asFiber_iso_hom_iff`, which handle an isomorphism of squares whose base also moves.

## Watch for

- The transport statement is one direction only, from `S'` to `S`, and assumes `LocallyOfFinitePresentation` of the normalized structure morphism over `S`; the one over `S'` is deduced.
- The normalizations depend on the finiteness witnesses `h₁`, `h₂`, which are propositions.
- The base morphism is passed as `j` with an equation `j = s ≫ i` rather than as the composite.

## References

Tags 09IL and 035Q.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreBaseIso.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
