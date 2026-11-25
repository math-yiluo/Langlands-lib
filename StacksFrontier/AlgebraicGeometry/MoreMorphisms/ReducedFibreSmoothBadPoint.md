# Smoothness of the normalized base change over a solved bad point

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothBadPoint`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a Nagata Dedekind domain with fraction field `K`, `g : Y ⟶ Spec R` flat, quasi-compact and locally of finite type with `Y` normal, `K₁/K` finite and `B = integralClosure R K₁`. Let `y` be a point of the normalization `Y₁` of the base change of `Y` to `Spec B` that is generic in its fibre over `Spec B`, over a nonzero prime, and `x` the point of `Y` below it, with local ring `O`. The file shows: if `K₁` is a solution for the extension of discrete valuation rings `R_x → O`, then `Y₁ ⟶ Spec B` is smooth at `y`. This is the second half of the last paragraph of the proof of the reduced fibre theorem (Tag 09IL).

## Main results

- `algebraStalkOfBase`, `isScalarTower_algebraStalkOfBase`, `isScalarTower_algebraStalkFractionRing`: the `R`-algebra structure on `O` given by the germ, and its compatibility with `R_x` and with `K → Frac O`.
- `isDomain_stalk_spec`, `isDiscreteValuationRing_stalk_spec`: the local ring of `Spec B` at a point is a domain when `B` is, and a discrete valuation ring at a nonzero prime of a Dedekind domain.
- `formallySmoothNAdic_localRingHom_of_isSolutionForStalk`: assuming `B` module-finite over `R`, at a bad point `x` (over a nonzero prime, generic in its fibre) with `IsSolutionForStalk`, for every maximal ideal `q` of the integral closure `T` of `O` in the reduction of `Frac O ⊗_K K₁`, the local map from `B` localized at the contraction of `q` to `T_q` is formally smooth for the adic topology of the maximal ideal (`RingHom.FormallySmoothNAdic`).
- `smoothAt_normalization_pullback_of_isSolutionForStalk`: the smoothness at `y` (`InfinitesimalLifting.SmoothAt`), given `hW`, that every quasi-compact open of the base change has finitely many irreducible components; module-finiteness of `B` over `R` is derived from the Nagata hypothesis `hR`.

## Proofs

The local ring of `Y₁` at `y` is the localization of `T` at a maximal ideal (from the companion maximal-prime file). The solution property, stated over `R_x`, is transported to the canonical base change and then descended from `integralClosure R_x K₁`, a localization of `B`, to `B` itself. The resulting adic formal smoothness feeds `smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ`.

## Watch for

- The bad-point conditions on `x` (`hs`, `hg`) and the solution `hsol` are hypotheses, stated at `x = pr₁ (ν y)`; the file does not derive the bad-point conditions from conditions on `y`, and `hsol` is a separate assumption.
- Smoothness at a point and adic formal smoothness are library notions.
- `IsSolutionForStalk` is made `@[expose]` so its package can be destructured here.

## References

Tags 09IL, 09EM, 09EN.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreSmoothBadPoint.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
