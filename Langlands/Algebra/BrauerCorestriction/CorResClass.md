# Corestriction after restriction

Let `L/K` be a finite separable extension, with `K` and `L` in one universe. This module proves the restriction–corestriction formula on the actual Brauer groups:

`Cor_{L/K}(Res_{L/K} x) = [L : K] • x` for every `x ∈ Br(K)`.

Here `Res_{L/K}` is the actual scalar-extension homomorphism `scalarExtension L` (`Langlands.Algebra.BrauerScalarExtension`), which sends the class of `B` to the class of `L ⊗_K B`. `Cor_{L/K}` is `corHom K L`. The notation is additive. There is no restriction on the characteristic, and `K` need not be infinite.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Tensor powers.** Let `B` be an actual central simple `K`-algebra (`CSA K`) and `E` a finite type.

- `piCSA E B` is the tensor power `⨂_K (i : E), B` as an actual central simple `K`-algebra (`CentralSimple`).
- `piReindexAlgEquiv` reindexes a tensor power along a bijection of index types.
- `piEmptyAlgEquiv` identifies the empty tensor power with `K`.
- `piOptionAlgEquiv` splits `⨂_{Option α} B ≃ (⨂_α B) ⊗_K B`.
- `classOf_piCSA` computes `classOf (piCSA E B) = |E| • classOf B`.

**Restriction and corestriction.**

- `classOf_corCSA_baseChange` computes `classOf (corCSA K L (baseChange L B)) = [L : K] • classOf B`.
- `corHom_scalarExtension` states `corHom K L (scalarExtension L x) = [L : K] • x`.
- `corHom_comp_scalarExtension` states the same identity for additive homomorphisms: `(corHom K L).comp (scalarExtension L) = [L : K] • id`.

## Implemented proof

**Tensor powers.** The proof is induction over finite types (`Finite.induction_empty_option`), using the class lemmas of `Langlands.Algebra.BrauerGroup`.

- *Reindexing.* Mathlib's `reindex` is multiplicative and unital (`PiTensorSemilinear.reindex_mul`, `reindex_one`), so isomorphic tensor powers have the same class.
- *Empty index.* The structure map `K →` (empty tensor power) is bijective, so the class is that of the ground field, which is `0`.
- *Adding an index.* `Option α` splits off one factor through `reindex`, `tmulEquivDep` and `subsingletonEquiv`. The resulting linear equivalence is an algebra map by `liftAlgHom`. So `classOf (piCSA (Option α) B) = classOf (piCSA α B) + classOf B`, by `classOf_tensor`. Finally `Finite.card_option` and `succ_nsmul` give the count.

**The formula.** Let `N` be the canonical closure and `E = L →ₐ[K] N`.

1. `CorRes` provides an actual `K`-algebra isomorphism from `corAlg K L N (L ⊗_K B) ⊗_K (⨂_E B)ᵐᵒᵖ` to a matrix algebra `M_r(K)` with `r > 0`.
2. Identity isomorphisms between bundled carriers and underlying algebras turn it into an isomorphism `tensor (corCSA K L (baseChange L B)) (opposite (piCSA E B)) ≃ M_r(K)`. These go through `corEquiv` from `Functoriality` and `Algebra.TensorProduct.congr`.
3. With `M_1(X) ≃ X` (`matrixFinOneAlgEquiv`), this is a Brauer equivalence with the ground field, so the class is `0`.
4. By the class lemmas of `Langlands.Algebra.BrauerGroup`, `classOf (corCSA K L (baseChange L B)) - classOf (piCSA E B) = 0`.
5. By `classOf_piCSA` and `natCard_algHom_canonicalClosure` (`|E| = [L : K]`), the class is `[L : K] • classOf B`.

Every Brauer class is the class of an actual representative, and on representatives `corHom` and `scalarExtension` hold by definition. This gives `corHom_scalarExtension`.

## Sources and scope

The restriction–corestriction formula `Cor ∘ Res = [L : K]` is the normalization proved here for Tits' tensor-descent corestriction. J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, defines the construction. For quadratic extensions the formula is M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), Proposition (3.13)(5), printed p. 37 / PDF p. 60: `N_{K/F}(A_K) ∼ A ⊗_F A`.

The proof here is an internal derivation valid for every finite separable extension. It rests on the permutation units of `PermUnits` and the splitting isomorphism of `CorRes`. The group law and the scalar-extension homomorphism come from `Langlands.Algebra.BrauerGroup` and `Langlands.Algebra.BrauerScalarExtension` and are not rebuilt.
