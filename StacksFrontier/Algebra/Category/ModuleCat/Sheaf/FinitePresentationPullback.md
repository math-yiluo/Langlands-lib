# Pullback preserves finite presentation

Module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, the file proves that the pullback `f^* G` of a sheaf of `𝒪_Y`-modules of finite presentation is again of finite presentation.

## Main result

- `Stacks.SheafOfModules.modulePullback_isFinitePresentation`: if `G` is a sheaf of `𝒪_Y`-modules with `G.IsFinitePresentation`, then `(modulePullback f).obj G` is of finite presentation.

## Construction and proof

Finite presentation is witnessed by quasi-coherent data: an open cover `Y = ⋃ Vᵢ` with a finite presentation of the restriction of `G` to each `Vᵢ`. The proof transports this witness along `f`:

- `preimage_opens_cover`: the preimages `f⁻¹(Vᵢ)` cover `X`.
- `pullbackPresentation`: a presentation stays a presentation after pullback along a continuous, final functor of sites, since pullback is a left adjoint and preserves the structure sheaf; generator and relation index types are unchanged, so finiteness is kept. For general sites the construction assumes that the pushforward of sheaves of modules is a right adjoint and that both sites have `HasWeakSheafify` and `WEqualsLocallyBijective` for abelian groups; the application to ringed spaces supplies these instances.
- `siteBaseChangeIso` and `pushforwardBaseChangeIso`: the square of sites `Opens Y ← (Opens Y)/V`, `Opens X ← (Opens X)/f⁻¹V` commutes, and so do the corresponding pushforwards.
- `pullbackOverFunctorIso`: restricting `f^* G` to `f⁻¹(V)` is the pullback of `G|_V` along the induced morphism of over-sites (`pullbackOverFunctor`); it is obtained by comparing the two composite adjunctions.
- `pullbackOverPresentation`: the resulting presentation of the restriction of `f^* G` to `f⁻¹(V)`.

Auxiliary instances record that the induced functor of over-sites is continuous (`overMap_isContinuous`) and that `Over.post G` is final (`post_final`). A last instance, `isRightAdjoint_sheafToPresheaf_opensOverOver`, records that on a doubly sliced site of opens the inclusion `sheafToPresheaf` of sheaves of abelian groups into presheaves is a right adjoint (its left adjoint is sheafification), to help instance search elsewhere.

## Watch for

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`: the space, the rings and the modules share one universe, the range in which the pullback functor `modulePullback` is available.

## References

Tag 01BQ.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01BQ](https://stacks.math.columbia.edu/tag/01BQ) | `modulePullback_isFinitePresentation` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationPullback.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
