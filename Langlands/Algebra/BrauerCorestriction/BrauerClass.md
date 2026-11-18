# The corestriction of Brauer classes

This module turns the tensor descent of `Construction` into a map on Mathlib's actual matrix-stable Brauer quotient (`Mathlib.Algebra.BrauerGroup.Defs`):

`cor K L : BrauerGroup L → BrauerGroup K`,

for a finite separable extension `L/K` with `K` and `L` in the same universe. The class of an actual central simple `L`-algebra `A` goes to the class of the actual central simple `K`-algebra `corAlg K L N A`, where `N` is the canonical closure. This value holds by definition.

The module proves:

- the descent is multiplicative: `Cor(A) ⊗ Cor(B) ≃ Cor(A ⊗ B)`;
- it is compatible with matrix stabilization;
- it respects Brauer equivalence;
- the class does not depend on the auxiliary closure;
- split classes go to split classes.

The ground field may have any characteristic and need not be infinite. The group law on Brauer classes is not used. Statements that the map is a homomorphism and that `Cor ∘ Res = [L:K]` are not proved here.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`. Let `e = #(L →ₐ[K] N)`.

**Multiplicativity and matrix stabilization.** The hypotheses are: `L/K` finite, `N/K` finite Galois, and `A`, `B` finite-dimensional central simple over `L`.

- `corMul_bijective` says that the comparison homomorphism `corMul K L N A B : corAlg A ⊗[K] corAlg B → corAlg (A ⊗[L] B)` from `Functoriality` is bijective.
- `corMulEquiv K L N A B : corAlg K L N A ⊗[K] corAlg K L N B ≃ₐ[K] corAlg K L N (A ⊗[L] B)` is the resulting actual `K`-algebra isomorphism.
- `corAlgMatrixStab K L N A n` is a `K`-algebra isomorphism `corAlg K L N (M_n(A)) ≃ₐ[K] M_{n^e}(corAlg K L N A)`, for `n ≠ 0`.
- `matrixFinOneAlgEquiv R X : Matrix (Fin 1) (Fin 1) X ≃ₐ[R] X` is an auxiliary identification of `1 × 1` matrices.

**Central simple representatives and Brauer classes.** Here `K`, `L` and `N` are in one universe `u`, and `L/K` is finite.

- `corCSAOf K L N A`, for `A : CSA L` and `N/K` finite Galois, is the actual algebra `corAlg K L N A` bundled as `CSA K`. Its instance fields are `isCentral_corAlg`, `isSimpleRing_corAlg` and `finiteDimensional_corAlg` from `CentralSimple`.
- `corCSA K L A` is `corCSAOf K L (canonicalClosure K L) A`, the corestriction representative.
- `corCSAOf_isBrauerEquivalent`: if `A` and `B` are Brauer equivalent, so are `corCSAOf K L N A` and `corCSAOf K L N B`.
- `isBrauerEquivalent_of_algEquiv`: isomorphic central simple algebras are Brauer equivalent.
- `cor K L`, for `L/K` finite separable, is the map `BrauerGroup L → BrauerGroup K` induced on Mathlib's quotient `Quotient (Brauer.CSA_Setoid _)`.
- `cor_mk` computes the class: `cor K L ⟦A⟧ = ⟦corCSA K L A⟧`. It holds by definition.
- `cor_mk_eq_of_closure` gives independence of the closure. For every finite Galois `N/K` with exactly `[L : K]` embeddings of `L`, `cor K L ⟦A⟧ = ⟦corCSAOf K L N A⟧`.
- `corCSAOf_matrix_split`: if `A ≃ₐ[L] M_n(L)` with `n ≠ 0`, then `corCSAOf K L N A` is isomorphic to `M_{n^e}(K)`.
- `cor_groundField`: the class of the ground field `L` goes to the class of the ground field `K`. The representatives are Task 7532's `Langlands.Brauer.groundField`. So the split class goes to the split class.

## Implemented proof

**Bijectivity of `corMul`.** The source is a tensor product of two finite-dimensional central simple `K`-algebras (`CentralSimple`). It is simple by the published `Langlands.CentralSimple.isSimpleRing_tensor` from Task 7532. The target is nontrivial because its dimension `(dim_L (A ⊗ B))^e` is positive. So the ring homomorphism is injective (`IsSimpleRing.injective_ringHom_or_subsingleton_codomain`).

By `Module.finrank_tensorProduct` and `finrank_corAlg_eq_pow`, both sides have dimension `(dim_L A)^e (dim_L B)^e = (dim_L A · dim_L B)^e`. Injectivity then gives surjectivity (`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`).

The ring and module structures of these subalgebras of tensor products are supplied with explicitly named arguments. Mathlib's `PiTensorProduct` additive group structure is not reducibly the same as its additive monoid structure, so instance search does not find them unaided. This does not affect the mathematics.

**Matrix stabilization.** The isomorphism is the composite of:

1. `corEquiv` applied to Mathlib's `matrixEquivTensor (Fin n) L A : M_n(A) ≃ A ⊗[L] M_n(L)`;
2. the inverse of `corMulEquiv` for `A` and `M_n(L)`;
3. `corAlgMatrixEquiv` from `Split` on the second factor, giving `corAlg (M_n(L)) ≃ M_{n^e}(K)`;
4. the inverse of `matrixEquivTensor` over `K`.

**Brauer equivalence.** Suppose `M_n(A) ≃ M_m(B)` with `n, m ≠ 0`. Then

`M_{n^e}(Cor A) ≃ Cor(M_n(A)) ≃ Cor(M_m(B)) ≃ M_{m^e}(Cor B)`,

using `corAlgMatrixStab` twice and `corEquiv` of the given isomorphism, and `n^e, m^e ≠ 0`. This is exactly Mathlib's `IsBrauerEquivalent`. So `Quotient.lift` defines `cor`, and `cor_mk` holds by `rfl`.

**Independence.** `nonempty_corAlgEquiv_canonical` from `Independence` gives an actual `K`-algebra isomorphism between the descents over the canonical closure and over `N`. Isomorphic algebras are Brauer equivalent with `n = m = 1`, via `AlgEquiv.mapMatrix`.

**Split classes.** `corCSAOf_matrix_split` composes `corEquiv` of the given isomorphism with `corAlgMatrixEquiv`. For `cor_groundField`, apply it with `n = 1`, using `L ≃ M_1(L)` from `matrixFinOneAlgEquiv`. Then compose `M_1(Cor L) ≃ Cor L ≃ M_{1^e}(K)` to witness Brauer equivalence with the ground field `K`.

## Sources and scope

J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13, defines the corestriction class of a central division algebra by formula (1), `[D] = Cor [D₁]`, where `D` is the fixed algebra of the tensor product of conjugates. The Remarque on printed p. 209 / PDF p. 14 says this formula can be taken as the definition of corestriction. This module takes it as the definition on actual central simple representatives. It proves that the definition is compatible with matrix stabilization, which Tits does not discuss because he works with division algebras.

Tits assumes `k` infinite in §5.3. That hypothesis is not needed by the construction here, so it is not imposed. The group structure on `BrauerGroup` belongs to Task 7532. Only its published tensor-closure theorem and the `groundField` representative are used here. The homomorphism property and the restriction–corestriction formula are separate later units.
