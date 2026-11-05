# Integrality of the parameters of ordered products of root exponentials

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.Integrality`, namespace `LieRootData`.

## Declarations

- `Supp A W`: the matrix `A` moves weights only by elements of `W`, that is,
  `A c d ≠ 0 → wt c - wt d ∈ W`. Calculus: `supp_zero`, `Supp.mono`, `Supp.add`, `Supp.smul`,
  `Supp.mul` (weight differences add), `supp_sum`, `supp_em` (`e_k^{(i)}` moves weights by
  `i • root k`).
- `divExp_decomp`: `x_k(f) = 1 + f E_k + Σ_{i < n} f^{i+2} e_k^{(i+2)}`; `supp_tail` bounds the
  `h`-level of the tail.
- `bigSet P h ε`: the elements `x` with `h(x) ≥ h(root ε)` and `x ≠ root ε`; `mem_bigSet_of_lt`
  and `add_mem_bigSet` (closed under addition when `h(root ε) > 0`).
- `supp_divExp_sub_one` and `supp_prod_sub_one`: if `h(root ε) > 0`, then for every root
  exponential of a root `θ ≠ ε` with `h(θ) ≥ h(ε)`, and for every ordered product of such
  exponentials, the difference from `1` is supported in `bigSet P h ε`.
- `prod_cons_apply`: in `x_ε(f) x_{θ₂}(f₂) ⋯` with all `θ_i ≠ ε` and `h(θ_i) ≥ h(ε) > 0`, the
  entry at `(c, d)` with `wt c = wt d + root ε` equals `f (E_ε)_{c d}`.
- `exists_int_sum_eq_one`: the entries of `E_k = e k 1` generate the unit ideal of `ℤ`: some
  integer combination `Σ a_{cd} (E_k)_{cd}` equals `1`. Otherwise the ideal is `(g)` with
  `|g| ≠ 1`. Some prime `p` divides `g` (Mathlib `Int.exists_prime_and_dvd`), so `p` divides all
  entries, contradicting `e_one_map_ne_zero`.
- `mul_mem_apply` and `divExp_mem_apply`: entries in a subring `Z` are preserved by products
  and by root exponentials with parameters in `Z`.
- `mem_of_prod_mem` (**integrality peeling**; `S` a commutative ring, `Z ⊆ S` a subring,
  `h : X →+ ℤ`): consider an ordered product `∏_{(θ, f) ∈ L} x_θ(f)` whose roots are `h`-positive
  and pairwise distinct, with nondecreasing `h`-values. If all its entries lie in `Z`, then every
  parameter `f` lies in `Z`.

Proof of `mem_of_prod_mem`: induction on `L`. For the first factor `x_ε(f)`,
`prod_cons_apply` and `exists_int_sum_eq_one` give `f = Σ a_{cd} (entry (c, d) of the
product)` over the pairs `(c, d)` with `(E_ε)_{cd} ≠ 0`. These pairs satisfy
`wt c = wt d + root ε` (`e_weight`), so `f ∈ Z`. Then `x_ε(-f)` times the product is the
remaining product. Its entries lie in `Z` by `divExp_mem_apply` and `mul_mem_apply`, and the
induction hypothesis applies.

Provenance: internal proof route. It replaces the integrality argument for the structure
constants of the commutator formula in Steinberg, *Lectures on Chevalley groups*, §3. The input
is primitivity of `E_k` modulo every prime, which holds in an admissible lattice.
