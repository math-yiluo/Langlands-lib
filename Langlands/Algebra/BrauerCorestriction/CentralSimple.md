# Central simplicity of the tensor descent

This module proves that the tensor-descent algebra `corAlg K L N A` from `Langlands.Algebra.BrauerCorestriction.Construction` is a finite-dimensional central simple `K`-algebra. The hypotheses are:

- `L/K` is finite;
- `A` is a finite-dimensional central simple `L`-algebra;
- `N/K` is finite Galois.

Neither infiniteness of `K` nor any condition on the characteristic is used. Simplicity of the fixed algebra uses separability of `N/K`, which is part of `IsGalois`. The result holds for every finite Galois `N`, whether or not `N` contains a normal closure of `L`.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Finite tensor products of central simple algebras.**

- `PiCentralSimple K ι` is the proposition that, for every family `B : ι → Type v` of finite-dimensional central simple `K`-algebras, the tensor product `⨂[K] i, B i` is central over `K` and a simple ring. It is the induction statement for the next result.
- `piTensor_isCentral_isSimpleRing K B`: for a finite index type `ι` and a family of finite-dimensional central simple `K`-algebras `B i`, `⨂[K] i, B i` is central and simple. Finite dimensionality is Mathlib's instance `PiTensorProduct.finite`.
- The three induction steps are `piCentralSimple_of_equiv` (transport along a bijection of index types), `piCentralSimple_empty` (empty index type) and `piCentralSimple_option` (adding one index).

**Conjugates.** Let `A` be a finite-dimensional central simple `L`-algebra and `σ : L →ₐ[K] N`. The following instances concern the conjugate `Conj A σ = N ⊗_{σ,L} A`:

- `conj_finiteDimensional` (from `Dimension`): it is finite-dimensional over `N`;
- `conj_isSimpleRing`: it is a simple ring;
- `conj_isCentral`: it is central over `N`.

**The tensor product of conjugates.** For `L/K` finite:

- `conjTensor_finiteDimensional`: `ConjTensor K L N A = ⨂_N σ, A^σ` is finite-dimensional over `N`;
- `conjTensor_isCentral`: it is central over `N`;
- `conjTensor_isSimpleRing`: it is a simple ring.

**The descended algebra.** For `N/K` finite Galois:

- `finiteDimensional_corAlg`: `corAlg K L N A` is finite-dimensional over `K`. This needs only finite dimensionality of `L/K` and of `A`.
- `isCentral_corAlg`: `corAlg K L N A` is central over `K`.
- `isSimpleRing_corAlg`: `corAlg K L N A` is a simple ring.

## Implemented proof

**Finite tensor products.** The proof is induction over finite types with `Finite.induction_empty_option`.

- **Transport.** For a bijection `e : α ≃ β`, Mathlib's `PiTensorProduct.reindex` along `e.symm` is a linear equivalence. It is multiplicative and unital (`PiTensorSemilinear.reindex_mul`, `reindex_one`), so it is a `K`-algebra equivalence. Centrality transfers by `Algebra.IsCentral.of_algEquiv` and simplicity by `IsSimpleRing.of_ringEquiv`.
- **Empty index.** Every element is `r • tprod f` for the unique empty family `f`, which equals `r • 1`. So the structure map `K → ⨂` is surjective. The tensor product is nontrivial because Mathlib's `isEmptyEquiv` identifies it linearly with `K`. Hence the structure map is a ring isomorphism. Simplicity comes from the field `K`, and centrality holds because every element is a scalar.
- **Adding an index.** Write `Option α ≃ α ⊕ PUnit` (`Equiv.optionEquivSumPUnit`). Compose `reindex`, the inverse of Mathlib's `tmulEquivDep` and `subsingletonEquiv` on the one-point factor. This gives a linear equivalence `⨂_{Option α} B ≃ (⨂_α B ∘ some) ⊗[K] B none`, sending `tprod f` to `tprod (f ∘ some) ⊗ f none`. Its composition with `tprod` is a multilinear map. That map preserves `1` and products of pure tensors (`tprod_mul_tprod`, `Algebra.TensorProduct.tmul_mul_tmul`), so `PiTensorProduct.liftAlgHom` makes it an algebra homomorphism. Its linear map agrees with the equivalence on pure tensors (`PiTensorProduct.ext`), so it is bijective and an algebra equivalence. The induction hypothesis and the binary results `Langlands.CentralSimple.isCentral_tensor` and `isSimpleRing_tensor` show that the right side is central simple, and this transfers back.

**Conjugates.** Finite dimensionality over `N` is `Module.Finite.trans` through `Twist σ`, where the base change `Twist σ ⊗[L] A` is finite. Simplicity is the Library theorem `Langlands.CentralSimple.isSimpleRing_baseChange L A (Twist σ)`. Centrality over `N` follows from `Langlands.CentralSimple.isCentral_baseChange L A (Twist σ)`. The center does not depend on the base ring, and the structure maps from `N` and from `Twist σ` are the same map `x ↦ x ⊗ 1`.

**Descent.** The tensor product of conjugates is central simple over `N` by the finite tensor theorem. The embeddings `L →ₐ[K] N` form a finite type because `L/K` is finite. The results for `corAlg` are `GaloisDescent.SemilinearAlgAction.finiteDimensional_fixedSubalgebra`, `isCentral_fixedSubalgebra` and `isSimpleRing_fixedSubalgebra`, applied to `galAction`.

## Sources and scope

Central simplicity of the fixed algebra is asserted in J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13: « L'ensemble E^Γ des points fixes de Γ dans E est une algèbre simple de centre k ». Tits states it for division algebras and the separable closure; the argument here is an internal derivation for finite Galois `N` and arbitrary finite-dimensional central simple `A`. That a tensor product of two central simple algebras is central simple is taken from Task 7532, `Langlands.Algebra.CentralSimpleTensor`. This module adds only the induction over finite index types. The standard statement is in M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §1, printed pp. 3–4 / PDF pp. 26–27.
