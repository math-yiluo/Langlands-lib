# The residue field of an algebraic APF extension

Module `FontaineWintenberger.APF.Tower.AlgebraicResidue`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with integer ring `𝒪[K]`, and `L/K` an algebraic extension, possibly infinite. The file studies the integral closure of `𝒪[K]` in `L`, identifies it with the ring of elements of spectral norm at most one, and shows that for an APF extension its residue field is already the residue field of a finite subextension.

## Definitions

- `integralClosureSpectralEquiv K L`: the `𝒪[K]`-algebra isomorphism `integralClosure 𝒪[K] L ≃ spectralIntegerRing K L`; it is the identity on underlying elements of `L`.
- `integralClosureInclusion K i` and `integralClosureResidueInclusion K i`: for a `K`-embedding `i : E → L` of algebraic extensions, the induced maps on integral closures and on their residue fields.
- `integralClosureSpectralResidueEquiv`: the induced isomorphism of residue fields over the residue field of `𝒪[K]`.
- `integralClosureResidueFromLayer K L E`: for a finite intermediate field `E`, the map from the residue field of `spectralIntegerRing K E` to the residue field of `integralClosure 𝒪[K] L`.
- `apfResidueLayer K L`: a finite intermediate field, chosen by `Classical.choose`, above which that map is bijective.
- `integralClosureResidueEquiv K L E hE`: the resulting isomorphism of residue fields for `E` above `apfResidueLayer K L`.

## Results

- `integralClosure 𝒪[K] L` is a valuation ring (instance `integralClosure_valuationRing`); `mem_or_inv_mem_integralClosure`; the map from `𝒪[K]` is local.
- `mem_integralClosure_inclusion_iff`, `mem_integralClosure_embedding_iff_spectral`: `i x` is integral over `𝒪[K]` exactly when `x` is, equivalently when `x` lies in the spectral integer ring of `E`.
- `integralClosureInclusion` is a local homomorphism, and the maximal ideal contracts to the maximal ideal (`integralClosureInclusion_maximalIdeal_comap`). Compatibility squares: `integralClosureSpectralEquiv_inclusion`, `integralClosureSpectralResidueEquiv_inclusion`.
- `exists_finiteIntermediateField_spectralResidue_preimage`: every residue class of `L` comes from a finite intermediate field.
- `IsAPF.exists_finiteIntermediateField_spectralResidueInclusion_bijective` and `IsAPF.exists_finiteIntermediateField_integralClosureResidue_bijective`: for `L/K` separable and APF with the residue field of `K` perfect, there is a finite intermediate field `T` such that for every finite `E ≥ T` the residue inclusion into `L` is bijective.
- `IsAPF.perfectField_integralClosureResidue`: under the same hypotheses the residue field of `integralClosure 𝒪[K] L` is perfect.

## Proofs

A residue class is represented by an element `x`, which lies in the finite field `K(x)`. Bijectivity combines this with the surjectivity of residue inclusions between large finite layers (`IsAPF.exists_finiteIntermediateField_residueInclusion_surjective`, from the file on residue stabilization): a class from a finite field `F` is moved into `E` through the compositum of `E` and `F`.

## Points to watch

- The stabilization results assume `PerfectField 𝓀[K]` and `L/K` separable; the first sections need only `L/K` algebraic.
- `apfResidueLayer` is a choice, not a canonical field.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1. The file's header says the finite-layer representative argument generalizes the one in `FalseTateExtension.Padic.FiniteGaloisStructure`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/AlgebraicResidue.lean` (SHA-256 of the source file `960649bf7e01a87515e7dd48568914b44bdef84455fa384e98b69797e3eeacd7`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
