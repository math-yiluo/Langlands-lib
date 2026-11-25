# The normalized base change of a normalized base change

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTower`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `g₀ : Spec B₀ ⟶ Spec A` be a morphism and `B₀ → B₁` a ring map, with `B₀`, `B₁` Noetherian, `B₀` Nagata and `Spec B₁ ⟶ Spec B₀` universally open, and let `f : X ⟶ Spec A` be quasi-compact and locally of finite type. With `W₀` the pullback of `f` along `g₀` and `Y₀` its normalization, the file shows that normalizing the base change of `Y₀` to `Spec B₁` gives the same as normalizing the base change `W₁` of `X` along `Spec B₁ ⟶ Spec B₀ ⟶ Spec A`. This composes the two finite extensions in the proof of the reduced fibre theorem (Tag 09IL).

## Main result

- `exists_normalizationScheme_iso_normalization_pullback_tower`: given witnesses `hW₀`, `hV`, `hW₁` that every quasi-compact open of each of the three schemes being normalized has finitely many irreducible components, there is an isomorphism from the normalization of `W₁` to that of the base change of `Y₀` to `Spec B₁`, over `Spec B₁`. Since it is over `Spec B₁`, it carries smoothness at a point from either side to the other.

## Proof

The library's comparison of iterated normalized base changes requires the scheme being normalized to be reduced, which `W₀` need not be. The argument therefore runs over the reduction of `W₀`: it has the same normalization as `W₀`, is of finite type over the Nagata base `B₀` and so has finite normalization, and the comparison applies to it. The base change of the reduction morphism to `Spec B₁` is a surjective closed immersion, which does not change the normalization, and the base change of `W₀` to `Spec B₁` is identified with `W₁`.

## Watch for

- The universal openness of `Spec B₁ ⟶ Spec B₀` and the Nagata property of `B₀` are hypotheses.
- The base change to `Spec B₁` is along the composite `Spec B₁ ⟶ Spec B₀ ⟶ Spec A`, not along `Spec` of `A → B₁`.

## References

Tags 09IL, 035Q, 09IK.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreTower.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
