# Dominated factorizations and their faithfully flat descent

This module defines dominating coefficient matrices and dominated factorizations. It proves
that locally split modules have dominated factorizations, and that for flat modules dominated
factorizations descend along faithfully flat ring maps. It is part of the module-theoretic
step of the proof of `Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement`
(Stacks Project, Tag 05FT). Everything is in the namespace `Langlands.CommutativeAlgebra`.

## Provenance

The definitions and proofs are internal to this project; Worker 928 wrote them. The word
"dominates" follows Stacks Project Definition 10.88.2 (Tag 059B): a map `g : P → P'` dominates
`f : P → M` if `Ker (f ⊗ id_Q) ⊆ Ker (g ⊗ id_Q)` for every module `Q`. `Dominates x A` below is
this condition for the maps `R^ι → M`, `e_i ↦ x i`, and `R^ι → R^κ`, `e_i ↦ (A i k)_k`, with
the test modules restricted to one universe. Dominated factorizations are an elementary,
matrix-level stand-in for the Mittag-Leffler condition on flat modules, in the spirit of
Stacks Proposition 10.88.6 (Tag 059E). The Lean statements below use only finite tuples and
coefficient matrices. They do not use any Mathlib or Stacks notion of Mittag-Leffler modules,
and this file claims nothing about such notions.

## Definitions

Let `R : Type u` be a commutative ring and `M : Type v` an `R`-module.

- `Dominates.{w} x A`, for a tuple `x : ι → M` with `ι` a finite type in `Type` and
  coefficients `A : ι → κ → R` (`κ : Type`): for every `R`-module `N : Type w` and every
  `ν : ι → N` with `∑ i, x i ⊗ₜ[R] ν i = 0` in `M ⊗[R] N`, we have `∑ i, A i k • ν i = 0`
  for every `k`. The universe `w` of the test modules is an explicit parameter.
- `HasDominatedFactorizations.{w} R M`: for every `n : ℕ` and every `x : Fin n → M` there are
  `m : ℕ`, `A : Fin n → Fin m → R` and `y : Fin m → M` with `x i = ∑ k, A i k • y k` for every
  `i` and `Dominates.{w} x A`.

## Results

### `LocallySplit.hasDominatedFactorizations`

If `LocallySplit R M`, then `HasDominatedFactorizations.{w} R M` for every universe `w`.

*Proof.* Given `x`, take `r`, `φ`, `y` from `LocallySplit` and set `A i j := φ (x i) j`; then
`x i = ∑ j, A i j • y j` holds by hypothesis. For domination, let
`∑ i, x i ⊗ₜ ν i = 0` in `M ⊗[R] N`. Apply `rTensor N` of the `j`-th coordinate of `φ`, followed
by the isomorphism `R ⊗[R] N ≃ N` (`TensorProduct.lid`). This gives `∑ i, φ (x i) j • ν i = 0`.

### `exists_eq_sum_smul_one_tmul`

Let `R'` be an `R`-algebra. Every `t : R' ⊗[R] M` can be written as
`t = ∑ j, c j • (1 ⊗ₜ z j)` with finitely many `c j : R'` and `z j : M`. The proof is by
induction on `t`, with `Fin.append` for sums.

### `exists_dominated_factorization_of_baseChange` (the descent step)

Assume `R → R'` is faithfully flat (`Module.FaithfullyFlat R R'`, with `R' : Type u'`) and
`M` is flat over `R`. Let `x : Fin n → M`, `z : κ → M` (`κ` a finite type in `Type`) and
`B : Fin n → κ → R'`. Assume:

1. `1 ⊗ₜ x i = ∑ l, B i l • (1 ⊗ₜ z l)` in `R' ⊗[R] M` for every `i`;
2. for every `R`-module `N : Type w` and `ν : Fin n → N` with `∑ i, x i ⊗ₜ ν i = 0`, we have
   `∑ i, B i l • (1 ⊗ₜ ν i) = 0` in `R' ⊗[R] N` for every `l`.

Then `x` has a dominated factorization over `R`: some `m`, `A : Fin n → Fin m → R` and
`y : Fin m → M` satisfy `x i = ∑ k, A i k • y k` and `Dominates.{w} x A`.

*Proof.*

1. For each `i`, hypothesis 1 says that the tensor
   `x i ⊗ 1 + ∑ l, z l ⊗ (-B i l)` vanishes in `M ⊗[R] R'`. Since `R'` is flat over `R`, the
   inclusion into `M` of the span of the elements `x i`, `z l` stays injective after tensoring
   with `R'`. So the relation vanishes trivially
   (`TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective`).
   This gives finitely many vectors `a i o : R^(k i)` (indexed by `o : Option κ`, with `none`
   standing for `x i` and `some l` for `z l`) and elements `y' i j : R'`. They satisfy
   `∑ o, a i o j • (x i or z l) = 0` in `M`, and the coefficient `1` resp. `-B i l` equals
   `∑ j, a i o j • y' i j`.
2. Collect all these relations into one linear map `f : R^K → R^(n ⊕ κ)` with
   `X ∘ f = 0`, where `X : R^(n ⊕ κ) → M` is the linear combination of `x` and `z`. By the
   equational criterion for flatness of `M`
   (`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`), `X` factors as
   `X = y₀ ∘ a₀` through a finite free module `R^m` with `a₀ ∘ f = 0`.
3. Set `A i k := a₀ (e_{x i}) k` and `y k := y₀ (single k 1)`. Then
   `x i = X (e_{x i}) = ∑ k, A i k • y k`.
4. From `a₀ ∘ f = 0` and step 1 one gets, in `R'`, the identity
   `algebraMap (A i c) = ∑ l, B i l * algebraMap (C l c)`, where `C l c := a₀ (e_{z l}) c`.
5. Domination: let `∑ i, x i ⊗ₜ ν i = 0` in `M ⊗[R] N`. Because `R'` is faithfully flat, the map
   `N → R' ⊗[R] N`, `ν ↦ 1 ⊗ₜ ν`, is injective (`Module.FaithfullyFlat.tensorProduct_mk_injective`).
   It therefore suffices to show `∑ i, 1 ⊗ₜ (A i c • ν i) = 0`. By step 4 this sum equals
   `∑ l, algebraMap (C l c) • ∑ i, B i l • (1 ⊗ₜ ν i)`, which vanishes by hypothesis 2.

### `hasDominatedFactorizations_of_baseChange`

With `R → R'` faithfully flat and `M` flat over `R`:
`HasDominatedFactorizations.{max u' w} R' (R' ⊗[R] M)` implies
`HasDominatedFactorizations.{w} R M`.

*Proof.* Given `x : Fin n → M`, take a dominated factorization `1 ⊗ₜ x i = ∑ k, A' i k • y' k`
over `R'`. Write each `y' k = ∑ j, c k j • (1 ⊗ₜ z k j)` by `exists_eq_sum_smul_one_tmul`, and
apply the descent step with the tuple `z` indexed by `Σ k, Fin (p k)` and
`B i ⟨k, j⟩ := A' i k * c k j`. Hypothesis 1 is a rearrangement of sums. For hypothesis 2, let
`∑ i, x i ⊗ₜ ν i = 0` in `M ⊗[R] N`. Base change to `R'` and the isomorphism
`R' ⊗[R] (M ⊗[R] N) ≃ (R' ⊗[R] M) ⊗[R'] (R' ⊗[R] N)`
(`TensorProduct.AlgebraTensorModule.distribBaseChange`) give
`∑ i, (1 ⊗ₜ x i) ⊗ₜ (1 ⊗ₜ ν i) = 0`. Domination over `R'`, tested against the `R'`-module
`R' ⊗[R] N` in universe `max u' w`, gives `∑ i, A' i k • (1 ⊗ₜ ν i) = 0`, and hence
hypothesis 2.
