# Naturality of the relative idele comparison under field isomorphisms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The ordinary adele ring of a finite extension `L/K` of number fields is obtained from the relative presentation `𝔸_K ⊗[K] L` by the comparison isomorphism `relativeAdeleBaseChangeRingEquiv`, and the ordinary idele group from its unit group by `relativeIdeleBaseChangeMulEquiv`. The file shows that this comparison, and with it the idele-class norm, is natural when `K` and `L` are replaced by isomorphic number fields `K'` and `L'`. Throughout, `eK : K ≃ₐ[ℚ] K'` and `eL : L ≃ₐ[ℚ] L'` are isomorphisms compatible with the embeddings, in the sense of a hypothesis `h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)`.

## Main results

- Functoriality of transport along isomorphisms: `relativeAdeleCongr_trans`, `adeleCongr_trans`, `ideleCongr_trans` and `ideleClassCongr_trans` say that transporting along `e` and then `f` is transporting along `e.trans f`, for relative adeles over `ℚ`, adeles, ideles and idele classes; `ideleClassCongr_refl` says transport along the identity is the identity.
- `relativeAdeleCongrOfAlgEquiv_towerActual`: a technical step comparing the compatible transport of the tower model `(𝔸_ℚ ⊗[ℚ] K) ⊗[K] L` with transport of its flattened presentation over `ℚ`.
- `relativeAdeleBaseChangeRingEquiv_congrOfAlgEquiv`: the comparison `𝔸_K ⊗[K] L ≃ 𝔸_L` intertwines the relative transport `relativeAdeleCongrOfAlgEquiv eK eL h` with the transport `adeleCongr eL` of adele rings.
- `relativeIdeleBaseChangeMulEquiv_congrOfAlgEquiv` and `relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv`: the same statement for ideles and for idele classes.
- `ideleClassCongr_ideleClassNorm`: the idele-class norm is natural: transporting `ideleClassNorm K L c` along `eK` gives `ideleClassNorm K' L'` of the transport of `c` along `eL`.

## Proofs

The naturality of the comparison passes through the fixed-bottom tower `(𝔸_ℚ ⊗[ℚ] K) ⊗[K] L`, the functoriality statements through the one-step presentation `𝔸_ℚ ⊗[ℚ] K`; both use only tensor-product coherence and induction on pure tensors, and no description of local components is involved. The naturality of the norm combines the comparison of relative and ordinary class norms (`ordinaryIdeleClassNorm_relativeIdeleClassBaseChange`) with the naturality of the relative class norm (`relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm`), both imported.

## Points to watch

The isomorphisms are `ℚ`-algebra isomorphisms between possibly different types, and the compatibility `h` is required in every statement about the pair `(K, L)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/TowerAlgEquivNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `2770d1e36a91ed120e51621e54a72ae8adc4d3c0386430952990d21f09ac6d27`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
