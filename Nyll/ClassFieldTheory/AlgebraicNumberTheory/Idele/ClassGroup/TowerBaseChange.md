# The tower model of ideles versus the relative model over the intermediate field

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a tower of finite extensions of number fields `K ⊆ M ⊆ L`, the library's tower model presents the ideles of `L` as units of `(𝔸_K ⊗[K] M) ⊗[M] L`. This file compares that model with the relative idele group `(𝔸_M ⊗[M] L)ˣ` of `L/M`, passing through the ordinary ideles of `L`, and deduces transitivity of the ordinary idele-class norm in any finite tower.

## Ring and idele comparisons

- `intermediateRelativeAdeleBaseChangeAlgEquiv`: `𝔸_K ⊗[K] M ≃ₐ[M] 𝔸_M`; tensoring with `L` gives `towerActualRelativeAdeleRingEquiv : (𝔸_K ⊗[K] M) ⊗[M] L ≃+* 𝔸_M ⊗[M] L`.
- `relativeAdeleBaseChangeRingEquiv_tower`: the two routes from the tower model to `𝔸_L` (through `𝔸_M ⊗[M] L`, or by flattening to `𝔸_K ⊗[K] L`) agree. It is checked component by component at finite and infinite places of `L`, using transitivity of completion maps.
- `towerRelativeIdeleBaseChangeMulEquiv`: the induced isomorphism of idele groups; it equals the comparison through ordinary ideles (`towerRelativeIdeleBaseChangeMulEquiv_eq_viaOrdinary`), preserves principal ideles, sends the extension of a relative idele of `M` to its inclusion over `M`, and turns conjugation by `σ ∈ Aut(L/M)`, viewed over `K`, into conjugation over `M`.
- `towerRelativeIdeleClassBaseChangeMulEquiv`: the tower class group is isomorphic to the relative idele class group of `L/M`, compatibly with the ordinary class group of `L` (`relativeIdeleClassBaseChangeMulEquiv_tower`) and with the action of `Aut(L/M)` (`towerRelativeIdeleClassBaseChangeMulEquiv_smul`).

## Norms

- Local component maps of tower ideles at finite and archimedean places of `M`, and at an extension `uM` to `M` of a finite place `w` of `K` (`towerIntermediateFiniteComponent`); `towerIntermediateFiniteComponent_norm` says the determinant norm commutes with the latter.
- `towerRelativeIdeleBaseChangeMulEquiv_norm`: the tower determinant norm corresponds to the relative norm of `L/M`; on class groups, `towerRelativeIdeleClassBaseChangeMulEquiv_classNorm`.
- `intermediateClassNormQuotientBaseChangeMulEquiv`: the tower quotient `IntermediateClassNormQuotient K M L` is isomorphic to the relative class-norm quotient of `L/M`.

## Transitivity of ordinary norms

- `ordinaryIdeleClassNorm_tower`: for the ordinary idele class groups, `ideleClassNorm K M (ideleClassNorm M L c) = ideleClassNorm K L c`.
- `ordinaryIdeleClassNorm_range_le_of_tower`: the image of `ideleClassNorm K L` is contained in the image of `ideleClassNorm K M`.

Neither needs a normality hypothesis. Both transport determinant-norm transitivity from the tower model to the ordinary class groups, using the comparisons above and that of relative and ordinary norms (`ordinaryIdeleClassNorm_relativeIdeleClassBaseChange`).

## Points to watch

"Ordinary" idele class groups are the library's `IdeleClassGroup`, built on its restricted-product idele group; the comparison with Mathlib's idele class group is made elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/TowerBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `9fba0384fa5f8ef0fc498bd2537437978858b74f579e998ff8a9e99d6da37e13`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
