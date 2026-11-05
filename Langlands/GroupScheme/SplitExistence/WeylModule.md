# Small integral representations of `SL₂` (`WeylModule`)

Author: Worker 239.

This module gives explicit integral matrices for two kinds of representation of `2 × 2`
matrices. Over every commutative ring `R`, each kind is multiplicative, and its values at the
unipotent matrices are truncated exponentials of integral divided-power operators. Later modules
assemble these blocks into the representations along a root (`StringRep`, `BlockRep`).

## The divided-power modules `Γ^m(R²)` for `m ≤ 3`

- `gam m g` is the matrix of `g` on `Γ^m(R²)` in the basis `x^[r] y^[m−r]` (`r = 0, …, m`),
  where `g x = g₀₀ x + g₁₀ y` and `g y = g₀₁ x + g₁₁ y`. The definition writes out the four
  matrices for `m = 0, 1, 2, 3` entry by entry, and `gam m g = 1` for `m ≥ 4`.
- `gam_mul`, `gam_one`, `gam_map`: `gam m` is multiplicative on all `2 × 2` matrices, sends `1`
  to `1`, and commutes with ring homomorphisms. `gam_mul` is checked entrywise for each `m ≤ 3`
  by `fin_cases`, `simp` and `ring`.
- `gamE m k` and `gamF m k` are the integral `k`-th divided powers of the raising and lowering
  operators: `gamE m k` sends `x^[c] y^[m−c]` to `C(c+k, k) x^[c+k] y^[m−c−k]`, and
  `gamF m k` sends `x^[c] y^[m−c]` to `C(m−c+k, k) x^[c−k] y^[m−c+k]`. Both are defined for
  all `m`.
- `gamE_zero`, `gamF_zero`, `gamE_eq_zero`, `gamF_eq_zero` (for `k > m`), and `gamE_mul`,
  `gamF_mul`: the divided-power law `E^[a] E^[b] = C(a+b, a) E^[a+b]`. The product is
  computed as a single-term sum (`Fintype.sum_eq_single`) and closed with `Nat.choose_mul`.
- `gam_upper_four`, `gam_lower_four`, and their reindexed forms `gam_upper`, `gam_lower` (for
  any truncation length `N > m`, via the helper `sum_range_eq_of_eq_zero`): for `m ≤ 3`,
  `gam m [[1, s], [0, 1]] = Σ_k s^k E^[k]` and `gam m [[1, 0], [s, 1]] = Σ_k s^k F^[k]`, with
  the integral matrices mapped into `R`.
- `gamE_ne_zero`, `gamF_ne_zero`: `E^[k]` raises the index `r` by `k`, and `F^[k]` lowers it
  by `k`.
- `gamE_one_mul_gamF_one_sub`: for `m ≤ 3`, `[E, F]` is diagonal with entries `2r − m`.
- `gam_diag`: `gam m diag(t, u)` is diagonal with entries `t^r u^(m−r)`.
- `gam_weyl_ne_zero`: the matrix `gam m [[0, 1], [−1, 0]]` is supported on the antidiagonal
  `r + c = m`.

## The Cartan block of the adjoint representation

Fix a finite type `ι`, an index `i₀ : ι` and integers `c : ι → ℤ`. The lattice
`ℤ v₋ ⊕ ℤ v₊ ⊕ ℤ^ι` (index type `Fin 2 ⊕ ι`, with `0 = v₋` and `1 = v₊`) models the two root
vectors `v₋ = y^[2]`, `v₊ = x^[2]` of a root together with Cartan vectors `u_t`. The vector
`u_{i₀}` plays the role of `xy`, and `e u_t = c_t v₊`, `f u_t = c_t v₋`.

- `cart i₀ c g`: for `g = [[a, b], [γ, δ]]`, `v₊ ↦ a² v₊ + aγ u_{i₀} + γ² v₋`,
  `v₋ ↦ b² v₊ + bδ u_{i₀} + δ² v₋`, and `u_t ↦ u_t + c_t (ab v₊ + bγ u_{i₀} + γδ v₋)`.
- `cart_mul`: if `c i₀ = 2`, then `cart` is multiplicative on matrices of determinant one. The
  proof multiplies the block decompositions (`fromBlocks_multiply`) and checks each block with
  the two determinant equations.
- `cart_one`, `cart_map`.
- `cartE`, `cartF`: the divided powers `e v₋ = u_{i₀}`, `e u_t = c_t v₊`, `e v₊ = 0`,
  `e^[2] v₋ = v₊`, and symmetrically `f v₊ = u_{i₀}`, `f u_t = c_t v₋`, `f^[2] v₊ = v₋`. Both
  are `1` in degree `0` and `0` in degrees at least `3`.
- `cartE_zero`, `cartF_zero`, `cartE_eq_zero`, `cartF_eq_zero`, and `cartE_mul`, `cartF_mul`
  (the divided-power law, assuming `c i₀ = 2`), proved by case analysis on the degrees and
  blockwise entry computations.
- `cart_upper_three`, `cart_lower_three`, `cart_upper`, `cart_lower`: the values of `cart` at
  the unipotent matrices are the truncated exponentials of `cartE` and `cartF`.
- `cart_diag`: `cart diag(t, u)` is diagonal with entries `u²` on `v₋`, `t²` on `v₊`, and `1`
  on the Cartan vectors.
- `cartLevel = Sum.elim ![-1, 1] 0`: the level `−1` for `v₋`, `1` for `v₊` and `0` for the
  Cartan vectors. `cartE_ne_zero` and `cartF_ne_zero` say that `E^[k]` raises the level by
  `k` and `F^[k]` lowers it by `k`, and `cart_weyl_ne_zero` says that the Weyl matrix
  `[[0, 1], [−1, 0]]` negates the level.
- `cartE_one_mul_cartF_one_sub`: if `c i₀ = 2`, then `[E, F]` is diagonal with entries
  `2 · cartLevel`.

## Provenance

These are the standard integral forms of the irreducible `SL₂`-modules of highest weight at most
three, with the divided-power (Kostant) ℤ-form of the universal enveloping algebra acting
(Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§7.2 and 26.4;
Steinberg, *Lectures on Chevalley groups*, §2). The Cartan block is the restriction of the
adjoint representation to the span of `e_α`, `f_α` and a Cartan lattice, written in a basis
adapted to the integral lattice. The formulas were
derived for this project and are checked by computation in Lean; no literature statement is
used.
