# Prime witnesses and Frobenius targets for an embedded abelian extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K ⊆ F ⊆ E` with `K`, `F` nonarchimedean local fields, `F/K` finite separable with compatible valuations, `E/F` finite abelian, a `K`-embedding `j : E →ₐ[K] K^sep` and an `F`-isomorphism `e` from the separable closure of `F` to `K^sep`. For each `z ∈ Gal(E/F)^ab` the file builds a unit of `F` that is the norm of a prime element of a Frobenius fixed field (the prime witness), together with the Frobenius element of `Gal(E/F)^ab` that its norm-residue symbol should produce (the target).

## Definitions and results

- `abelianizationCongr_symm_eq_primeTarget`: a group-theoretic lemma. For isomorphisms `q₀ : Q₀ ≃* G₀` and `qE : Q₀ ≃* G` and `q ∈ Q₀`, if `r` is the image of `q` in `G₀^ab` under `q₀`, then pulling `r` back by `q₀` and pushing it forward by `qE` gives the image of `q` in `G^ab`.
- `ambientEmbeddedPrimeWitness K F E j e z : Fˣ`. Lift `z` to the extension quotient of the intrinsic presentation of `E/F`, which uses the embedding of `E` into the separable closure of `F` obtained from `j` and `e`. Choose a Frobenius element `σ` over `F` restricting to the lift, and let `L_F` be its Frobenius fixed field over `F`. Let `L_H` be the Frobenius fixed field in `K^sep` of the image of `σ` under `intrinsicFrobeniusElementToAmbientEmbeddedField`, and `φ : L_F ≃+* L_H` the isomorphism induced by `e`. Both fields get their spectral-norm local-field structures. `φ` preserves valuation subrings by `valuationSubring_mem_iff_of_separableClosureRingEquiv`. The witness is the norm to `F` of the unit of `L_F` chosen by `chosenValuationOneUnitOfRingEquiv` for `φ`.
- `ambientEmbeddedPrimeTarget K F E j e z`: the abelianized Frobenius restriction of the same transported `σ` in the ambient extension quotient, moved to `Gal(E/F)^ab` by `ambientEmbeddedExtensionQuotientEquivGaloisGroup`.

## Points to watch

- Apart from the group lemma, the file contains only constructions. It does not prove that the witness's norm-residue symbol equals the target, or that its Artin image is `z`.
- The lift of `z` and the Frobenius element are chosen with `Classical.choose`. Witness and target are written with the same choices, so they refer to the same `σ`.
- The local-field structures on the Frobenius fixed fields are the library's spectral-norm structures on finite extensions, not given data.
- Frobenius elements and fixed fields come from the library's `localResidueDatum`; the fields live in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeWitness.lean`: the Lean file is the source byte for byte (SHA-256 `11fef0519bb66c290406723e92ef2f56b1c67fd4e0e10b8323b32acdceb11e52`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
