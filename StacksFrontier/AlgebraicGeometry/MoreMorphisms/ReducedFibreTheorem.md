# The reduced fibre theorem

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTheorem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `A` be a Nagata Dedekind domain with fraction field `K` and `f : X ⟶ Spec A` flat, quasi-compact and locally of finite type. The file proves that there is a finite extension `L/K` such that, with `B` the integral closure of `A` in `L`, the normalization of the base change of `X` to `Spec B` is smooth over `Spec B` at every generic point of every fibre. `X` is assumed neither reduced, nor normal, nor affine.

## Main results

- `exists_ringEquiv_integralClosure_of_isIntegral`: for a tower `R → B → L` with `B` integral over `R`, the integral closures of `R` and of `B` in `L` are isomorphic rings, compatibly with the maps from `R`. They are equal subrings of `L` but different types.
- `smoothAt_asFiber_genericPoints_normalization_pullback_of_tower`: the two extensions of the proof compose. If `L₀/K` and `L₁/L₀` are finite, `B₀` is the closure of `A` in `L₀`, `Y₀` the normalization of the base change of `X` to `Spec B₀`, and the normalization of the base change of `Y₀` to `Spec B₁` (`B₁` the closure of `B₀` in `L₁`) is smooth at generic points of fibres, then so is the normalization of `X` base-changed to the closure of `A` in `L₁`.
- `exists_finiteExtension_smoothAt_asFiber_genericPoints_normalization_pullback`: the theorem with `K` in the scheme's universe, smoothness for every witness `hW`, and the generic-point condition read on points of the normalization lying over their image.
- `exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback` (Tag 09IL): the theorem, with `K` in an arbitrary universe and the condition stated for generic points `y` of each fibre over `b ∈ Spec B`.

## Proofs

The first paragraph of the proof (another file) replaces `A` by `B₀` and `X` by the normal `Y₀`, whose generic fibre has a dense smooth open; `B₀` is again Nagata and Dedekind. The last paragraph (another file) gives `L₁/L₀` with the smoothness for `Y₀`. Normalized base change along `A → B₀ → B₁` equals normalized base change along the composite, using that `Spec B₁ ⟶ Spec B₀` is universally open; smoothness and the generic-point condition move across that isomorphism, then across the ring isomorphism of bases between `integralClosure B₀ L₁` and `integralClosure A L₁`. For the final statement `K` is identified with `FractionRing A`.

## Watch for

- Smoothness at a point is the library's `InfinitesimalLifting.SmoothAt`.
- The Nagata hypothesis is explicit (`hA : StacksIsNagataRing A`); `A` is not assumed excellent.
- In the final statement the finiteness witness `hW` needed to name the normalization is part of the existential; it is proved, not assumed. The `A`-algebra structure on `L` is also existential, constrained by `IsScalarTower A K L`.
- The extension `L` lives in the scheme's universe `u`.

## References

Tags 09IL, 032T, 035Q.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09IL](https://stacks.math.columbia.edu/tag/09IL) | `exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreTheorem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
