# Base change of finite étale algebras along a separably closed extension

This module supplies the algebraic half of `HenselianFiniteEtaleEquivalenceStatement`. It works over any field extension `F/K` in which `K` is separably algebraically closed (`separableClosure K F = ⊥`). For a henselian valued field `K` and its completion `F = K̂`, this hypothesis is the published `separableClosure_completion_eq_bot`.

All results are in the namespace `HenselianFiniteEtale`.

## Roots of separable polynomials come from the base

* `mem_range_of_aeval_eq_zero` is the core of this section.
  * Setup: `M/K` is finite separable, and `E` is a field over `F` with `[E : F] = [M : K]`. `φ : M → E` is a `K`-algebra map, and `y ∈ E` is a root of a separable `p ∈ K[X]`.
  * Claim: `y ∈ φ(M)`.
  * Proof: `N = K(y) ⊔ φ(M)` is finite separable over `K`. So `F ⊗_K N` is a field (`HenselianTensorCompletion.isField_tensor`), and the multiplication map `F ⊗_K N → E` is injective. Comparing dimensions gives `[N : K] ≤ [M : K]`, so `N = φ(M)`.
* `exists_tmul_eq_of_field`: for a finite separable field `M`, a root `y ∈ F ⊗_K M` of a separable polynomial over `K` is `1 ⊗ m` for some `m ∈ M`.
  * As in `HenselianTensorCompletion.isField_tensor`, `F ⊗_K M ≅ F[X]/(f)` for the minimal polynomial `f` of a primitive element.
  * Apply the previous lemma in that field.
* `exists_tmul_eq`: the same for a finite étale `B`. Write `B` as a finite product of finite separable fields (`Algebra.Etale.iff_exists_algEquiv_prod`). Then `F ⊗_K B` is the product of the `F ⊗_K M_i` (`Algebra.TensorProduct.piRight`), and the field case applies in each factor.
* `exists_separable_aeval_eq_zero`: every element `a` of a finite étale `A` is a root of a separable polynomial over `K`. That polynomial is the product of the distinct minimal polynomials of the components of `a`. Distinct monic irreducible polynomials are coprime, so the product is separable (`Polynomial.separable_prod'`).

## Bijectivity on algebra maps

`bijective_map`: for finite étale `A` and `B`, the map `φ ↦ Algebra.TensorProduct.map (AlgHom.id F F) φ` is bijective.

* Injectivity: `b ↦ 1 ⊗ b` is injective (`Algebra.TensorProduct.includeRight_injective`).
* Surjectivity: let `ψ : F ⊗ A → F ⊗ B` be an `F`-algebra map. For each `a ∈ A`, `ψ(1 ⊗ a)` is a root of a separable polynomial over `K`, so it lies in the image of `B`. Hence `a ↦ ψ(1 ⊗ a)` factors through `B` (`AlgHom.codRestrict`, `AlgEquiv.ofInjective`), and its base change agrees with `ψ` on pure tensors (`Algebra.TensorProduct.ext'`).

## Reduction of essential surjectivity to fields

* `nonempty_algEquiv_of_algHom`: let `L/K` be finite separable, and let `E` be a field over `F` of dimension `[L : K]`. Any `K`-algebra map `L → E` induces an isomorphism `F ⊗_K L ≅ E`. The induced map is injective because its source is a field, and it is surjective by dimension count.
* `exists_etale_of_field`: suppose every finite separable field extension `E'/F` is `F ⊗_K L` for some finite separable `L/K`. Then every finite étale `F`-algebra `E` is `F ⊗_K A` for a finite étale `K`-algebra `A`. Decompose `E` into a finite product of fields `E_i`. Take `A = ∏ L_i`, which is étale by `Algebra.Etale.iff_exists_algEquiv_prod`. Then `F ⊗_K ∏ L_i ≅ ∏ F ⊗_K L_i ≅ ∏ E_i ≅ E`.
