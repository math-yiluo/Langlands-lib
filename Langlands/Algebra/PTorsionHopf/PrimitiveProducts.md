# Convolution of functionals on products of primitive elements

Author: Worker 1519, as internal infrastructure for the proof of
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`.

Provenance: internal. These are elementary computations with primitive elements
(`Bialgebra.IsPrimitiveElem k x`: `counit x = 0` and `comul x = 1 ⊗ x + x ⊗ 1`), written by
the author; no source statement is translated.

Notation: `k` is a field, `A` a commutative `k`-bialgebra, the convolution dual is
`WithConv (A →ₗ[k] k)`, and `augIdeal` is the ideal of functionals vanishing at `1`
(`AugmentationIdeal.md`). Products of primitive elements are indexed by finite sets `I` of an
arbitrary index type, with possibly repeated values.

## Products of primitive elements

- `add_apply'`: evaluation of a sum of functionals.
- `comul_prod_primitive I y hy`: if every `y v` (`v ∈ I`) is primitive, then
  `comul (∏ v ∈ I, y v) = ∑ T ⊆ I, (∏ v ∈ T, y v) ⊗ (∏ v ∈ I \ T, y v)`. The comultiplication
  is an algebra map and `Finset.prod_add` expands the product.
- `convMul_apply_prod`: consequently
  `(η * Θ) (∏ v ∈ I, y v) = ∑ T ⊆ I, η (∏ v ∈ T, y v) * Θ (∏ v ∈ I \ T, y v)`.

## Vanishing and the Leibniz expansion (cocommutative case)

Assume `Coalgebra.IsCocomm k A`.

- `apply_prod_eq_zero_of_card_lt y n`: every `Θ ∈ augIdeal ^ n` kills every product of fewer
  than `n` primitive elements. Induction on `n` through `augIdeal ^ (n+1) = augIdeal * augIdeal ^ n`
  and `Submodule.mul_induction_on`; in the expansion the term `T = ∅` contains `η 1 = 0` and
  the other terms involve shorter products.
- `convMul_apply_prod_eq_sum`: for `η ∈ augIdeal`, `Θ ∈ augIdeal ^ n` and `I` of cardinality
  `n + 1`, `(η * Θ) (∏ v ∈ I, y v) = ∑ v ∈ I, η (y v) * Θ (∏ w ∈ I.erase v, y w)`. In the
  expansion only the singletons `T = {v}` survive: `T = ∅` gives `η 1 = 0`, and `|T| ≥ 2`
  leaves fewer than `n` factors for `Θ`.

## Kronecker pairing

Let `r : ℕ`.

- `labelCount l I : Fin r → ℕ` counts, for labels `l : ι → Fin r`, the indices of `I` with
  each label. `labelCount_erase` and `labelCount_empty` record its behaviour.
- `prod_pow_mem_pow_sum`: a product of powers of elements of an ideal `J` (any commutative
  ring) lies in `J` raised to the total exponent.
- `dualMonomial ξ γ := ∏ i, ξ i ^ γ i` in the convolution dual; `dualMonomial_mem` puts it in
  `augIdeal ^ (∑ i, γ i)` when all `ξ i ∈ augIdeal`, and `dualMonomial_update` peels off one
  factor `ξ i` when `γ i ≠ 0`. `factorial_update` and `sum_update` are the matching identities
  for `∏ (γ j)!` and `∑ γ j`.
- `dualMonomial_apply_prod hb hξ hξb l n γ hγ I hI` (**Kronecker pairing**): let `b i` be
  primitive, `ξ i ∈ augIdeal` with `ξ i (b j) = if i = j then 1 else 0`. If `∑ γ i = n` and
  `I` has `n` elements, then
  `dualMonomial ξ γ (∏ v ∈ I, b (l v))` equals `∏ i, (γ i)!` (cast to `k`) when
  `labelCount l I = γ`, and `0` otherwise.

  Proof as implemented: induction on `n`. Choose `i` with `γ i ≠ 0`, write the monomial as
  `ξ i * dualMonomial ξ γ'` with `γ' = γ` lowered by one at `i`, apply the Leibniz expansion,
  keep the indices `v` with label `i`, use the induction hypothesis on `I.erase v`
  (`labelCount_erase`), and count: the `labelCount l I i` equal terms give
  `γ i * ∏ (γ' j)! = ∏ (γ j)!` exactly when `labelCount l I = γ`.
