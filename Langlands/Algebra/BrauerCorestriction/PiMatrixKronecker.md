# Kronecker identification of a finite tensor power of matrix algebras

Let `F` be a field, `E` a finite type and `m ≠ 0`. This module identifies the `E`-fold tensor power `⨂_F (σ : E), M_m(F)` with the matrix algebra whose rows and columns are indexed by functions `E → Fin m`:

`⨂_σ A_σ ↦ ((i, j) ↦ ∏_σ A_σ (i σ) (j σ))`.

It also proves the following.

- Reindexing the tensor factors along a permutation of `E` becomes reindexing the rows and columns.
- A ring homomorphism applied to all entries commutes with the identification.
- Permutation matrices are units, conjugation by them reindexes rows and columns, and they compose like the bijections.

These facts are used to build permutation units in tensor powers of central simple algebras (`PermUnits`). No hypothesis on the field is used.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**The Kronecker map.**

- `kroneckerMultilinear F E m` is the `F`-multilinear map `(A_σ)_σ ↦ ((i, j) ↦ ∏_σ A_σ (i σ) (j σ))` (`kroneckerMultilinear_apply`).
- `kroneckerMultilinear_one`: the family of identity matrices goes to the identity matrix.
- `kroneckerMultilinear_mul`: products of families go to products of matrices.
- `kroneckerHom F E m : (⨂[F] _ : E, Matrix (Fin m) (Fin m) F) →ₐ[F] Matrix (E → Fin m) (E → Fin m) F` is the induced algebra homomorphism (`kroneckerHom_tprod`).
- `finrank_piMatrix` computes `finrank F (⨂_E M_m(F)) = (m * m) ^ |E|`.
- `kroneckerHom_bijective` and `kroneckerEquiv F E m` give the algebra isomorphism, for `m ≠ 0`.

**Permutations and entrywise maps.**

- `indexPerm π`, for `π : Equiv.Perm E`, is the bijection `i ↦ i ∘ π⁻¹` of index functions (`indexPerm_symm_apply`).
- `kroneckerMultilinear_reindex`: the Kronecker matrix of `σ ↦ A (π⁻¹ σ)` is the Kronecker matrix of `A` with rows and columns reindexed by `(indexPerm π)⁻¹`.
- `kroneckerMultilinear_map`: for a ring homomorphism `f : F →+* F'`, the entrywise image of a Kronecker matrix is the Kronecker matrix of the entrywise images.
- `permUnit s`, for a bijection `s` of a finite index type, is the permutation matrix of `s` as a unit, with inverse the permutation matrix of `s⁻¹`.
- `permUnit_conj` computes `P_s X P_s⁻¹ = X.submatrix s s`.
- `permUnit_trans` computes `P_{s.trans t} = P_s * P_t`.
- `permUnit_map`: permutation matrices are fixed by every ring homomorphism applied to their entries.

## Implemented proof

**Multilinearity.** Each coordinate of the Kronecker map is a product of one entry from each factor. Updating one factor changes one term of the product: `Function.apply_update` and `Finset.prod_update_of_mem` isolate that term, and additivity and homogeneity follow.

**Unit and products.** The identity case is `Fintype.prod_boole`: the product of Kronecker deltas `δ(i σ, j σ)` over `σ` is `δ(i, j)`. The product case is `Finset.prod_univ_sum`: a product over `σ` of sums over `k_σ` equals the sum over functions `k : E → Fin m` of products, which is the matrix product indexed by functions. Mathlib's `PiTensorProduct.liftAlgHom` then gives the algebra homomorphism.

**Bijectivity.** The source is a finite tensor product of the finite-dimensional central simple algebras `M_m(F)`, so it is a simple ring (`piTensor_isCentral_isSimpleRing` of `CentralSimple`). The target is nontrivial, so the homomorphism is injective. Both sides have dimension `m^{2|E|}`: the source via `Basis.piTensorProduct` of matrix bases, the target via `Module.finrank_matrix`. Injectivity then gives surjectivity.

**Permutations.** The reindexing formula is `Fintype.prod_equiv π`. The entrywise formula is `map_prod`. For permutation matrices, Mathlib's `PEquiv.toMatrix_toPEquiv_mul` and `PEquiv.mul_toMatrix_toPEquiv` compute left and right multiplication as reindexing, and `PEquiv.toMatrix_trans` gives the composition law. Entries `0` and `1` are fixed by every ring homomorphism.

## Sources and scope

This is standard linear algebra: the Kronecker product of matrices for a finite tensor power, together with permutation matrices. It is an internal derivation from Mathlib's tensor-product and matrix API. It serves as the split model for the permutation units used to prove the restriction–corestriction formula. That argument generalizes the use of the switch map in M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), Proposition (3.13)(5), printed pp. 37–39 / PDF pp. 60–62.
