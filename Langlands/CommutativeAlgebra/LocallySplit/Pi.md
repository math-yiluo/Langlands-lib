# Locally split base changes along a finite product

This module proves two lemmas about the predicate `Langlands.CommutativeAlgebra.LocallySplit`
(defined in `Langlands.CommutativeAlgebra.LocallySplit.Basic`). They are used in the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
There, local splitness is first proved over each factor of a finite faithfully flat cover
`∀ i, A i` of the base ring, and these lemmas combine the factors.

## Statements

- `Langlands.CommutativeAlgebra.LocallySplit.of_fintype`: to prove `LocallySplit R M`, it is
  enough that for every `n` and `x : Fin n → M` there are a finite type `κ`, an `R`-linear map
  `φ : M →ₗ[R] (κ → R)` and `y : κ → M` with `∑ j, φ (x i) j • y j = x i` for all `i`. So the
  free module may be indexed by any finite type instead of `Fin r`.
- `Langlands.CommutativeAlgebra.locallySplit_pi`: let `R` be a commutative ring, `M` an
  `R`-module, `ι` a finite type with decidable equality, and `A i` (`i : ι`) commutative
  `R`-algebras. If `A i ⊗[R] M` is locally split over `A i` for every `i`, then
  `(∀ i, A i) ⊗[R] M` is locally split over `∀ i, A i`.

## Proofs

`LocallySplit.of_fintype`: transport along the equivalence `e : κ ≃ Fin (Fintype.card κ)`. That
is, take `LinearMap.funLeft R R e.symm ∘ₗ φ` and `y ∘ e.symm`, and reindex the sum with
`Equiv.sum_comp`.

`locallySplit_pi`: write `B = ∀ i, A i`. Let `π i : B ⊗[R] M → A i ⊗[R] M` be the `R`-linear map
`(LinearMap.proj i).rTensor M`, and let `σ i : A i ⊗[R] M → B ⊗[R] M` be
`(LinearMap.single R A i).rTensor M`. Induction on tensors proves three identities:

- `π i (b • m) = b i • π i m`;
- `σ i (a • z) = Pi.single i a • σ i z`;
- `∑ i, σ i (π i m) = m`, by `Finset.univ_sum_single`.

Given `x : Fin n → B ⊗[R] M`, apply the hypothesis for each `i` to the tuple `k ↦ π i (x k)`.
This gives `r i`, `φ i` and `y i` with `∑ j, φ i (π i (x k)) j • y i j = π i (x k)`. The finite
index type is `κ = Σ i, Fin (r i)`. Define the `B`-linear map
`Φ m ⟨i, j⟩ = Pi.single i (φ i (π i m) j)`. It is `B`-linear by the first identity and
`Pi.single_mul_right`. The elements are `⟨i, j⟩ ↦ σ i (y i j)`. Then
`∑ ⟨i, j⟩, Φ (x k) ⟨i, j⟩ • σ i (y i j) = ∑ i, σ i (∑ j, φ i (π i (x k)) j • y i j)` by the
second identity and `Fintype.sum_sigma`. This equals `∑ i, σ i (π i (x k)) = x k` by the third
identity. `LocallySplit.of_fintype` finishes the proof.

## Provenance

These lemmas are internal to the project and are not taken from the literature. Worker 281
proposed the statement of `locallySplit_pi` as the product step of the 05FT proof, and
Worker 928 proved it.
