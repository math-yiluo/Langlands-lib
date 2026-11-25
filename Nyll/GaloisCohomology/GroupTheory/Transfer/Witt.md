# Witt's transfer theorem

Module `Nyll.GaloisCohomology.GroupTheory.Transfer.Witt`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that for a finitely generated group `G` with finite abelianization, the transfer `G/G' → G'/G''` from `G` to its commutator subgroup `G'` is trivial. The proof is Witt's group-ring argument with Fox derivatives, built directly from free words.

## Main definitions

- `commutatorTransfer`: the transfer `Gᵃᵇ → (G')ᵃᵇ`, defined when `G'` has finite index (`FiniteIndex (commutator G)`), which is how the file expresses that `Gᵃᵇ` is finite (instance `finiteAbelianizationOfFiniteIndex`).
- `groupRingDelta g`: the element `[g] − 1` of `ℤ[G]`.
- `wordExponent w`: the exponent-sum vector `X →₀ ℤ` of a free word.
- `relationBasis`, `relationWord`, `foxCoefficient`: for a surjection `φ : F(X) → G` from a free group on a finite set, a basis of the relation lattice (the kernel of `ℤ^X → Gᵃᵇ`) indexed by `X`, a chosen relator word for each basis vector, and its right Fox coefficients.
- `foxMatrix`: the `X × X` matrix of these coefficients reduced to `ℤ[Gᵃᵇ]`.
- `groupNormElement Q`: the sum of all elements of a finite group `Q` in `ℤ[Q]`.

## Main results

- `commutatorTransfer_eq_one_of_finite_abelianization`: if `G` is finitely generated (`Group.FG G`) and `G'` has finite index, then `commutatorTransfer = 1`.
- `exists_rightFoxExpansion`: for every word `w`, `[φ w] − 1 = ∑ᵢ ([φ xᵢ] − 1) μᵢ` with the augmentation of `μᵢ` equal to the exponent sum of `xᵢ` in `w`.
- `presentationKernel_finrank_eq` and `exists_relationWord`: the relation lattice has full rank, and each of its vectors is the exponent vector of an actual relator.
- `natAbs_augmentation_foxMatrix_det`: the augmentation of `det(foxMatrix)` has absolute value `|Gᵃᵇ|`.
- `exists_unit_foxMatrix_det_eq_smul_norm`: `det(foxMatrix) = ±` the norm element of `Gᵃᵇ`.
- `delta_mul_transversalNormElement_mem_mixed`: `(g − 1) · ∑ρ` lies in `I(G) I(G')` for every `g` and every left transversal of `G'`.

Helper results include group-ring identities for `[g] − 1`, a determinant lemma, and the inclusion `I(G) · ker(ℤ[G] → ℤ[Gᵃᵇ]) ⊆ I(G) I(G')`.

## Proof

By the relators, the row vector with entries `[φ xᵢ] − 1`, taken in `ℤ[Gᵃᵇ]`, times `foxMatrix` is zero, so every `a − 1` kills the determinant in `ℤ[Gᵃᵇ]`; hence the determinant is an integer multiple of the norm element, and the augmentation computation forces the integer to be `±1`. Lifting to `ℤ[G]` gives `(g − 1)·∑ρ ∈ I(G) I(G')`, which the norm-element formula and the isomorphism `(G')ᵃᵇ ≅ (I(G') + I(G) I(G'))/I(G) I(G')` of the library's relative augmentation file turn into triviality of the transfer.

## Points to watch

- Finiteness of `Gᵃᵇ` enters as `FiniteIndex (commutator G)`.
- `I(G) I(G')` is the library's `mixedAugmentationProduct`, an additive subgroup of `ℤ[G]`.
- Relator words, the transversal and an additive section `ℤ[Gᵃᵇ] → ℤ[G]` are chosen noncomputably; the final statement does not depend on them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/Transfer/Witt.lean`: the Lean file is the source byte for byte (SHA-256 `ed9603eea32dbbe14424d823ee4d0bddd1a159757df8d958b4a54581110b244a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
