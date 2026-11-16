# Top symbols of words of first-order operators

## Definitions

- `OpData n`: data `(W, λ)` with `W : Lw n → Pol n` and `λ : Pol n`; `op d = Σ_p W_p ∂_{v_p} + λ`
  as a linear map of `Pol n`; `sym d = Σ_p W_p ξ_p` its symbol.
- `ellF = Σ_p v_p ξ_p`.
- `evalWord w`: the composition `op d₁ ∘ ⋯ ∘ op d_k` along a word `w = [d₁, …, d_k]`;
  `wcoeff w j`: the coefficients defined recursively by `wcoeff [] j = [j = 0]` and
  `wcoeff (d :: w) j = op d (wcoeff w j) + [j ≠ 0] sym d · wcoeff w (j - 1)`.

## Results

- `op_ell_pow_mul`: `op d (ℓ^r P) = ℓ^r op d P + r ℓ^{r-1} sym d P`.
- `evalWord_ell_pow`: `evalWord w (ℓ^m) = Σ_{j ≤ m} m(m-1)⋯(m-j+1) · ℓ^{m-j} · wcoeff w j`.
- `wcoeff_eq_zero_of_lt`, `wcoeff_length`: `wcoeff w j = 0` for `j > |w|`, and
  `wcoeff w |w| = ∏_{d ∈ w} sym d`.
- `sum_wcoeff_eq_zero`: if `Σ_i c_i evalWord (w_i) = 0` on `Pol n`, then
  `Σ_i c_i wcoeff (w_i) j = 0` for every `j` (induction on `m` in the expansion of `ℓ^m`, the
  top coefficient being `m! · (Σ_i c_i wcoeff (w_i) m)`).
- `sum_prod_sym_eq_zero`: in particular, if all words have length `≤ K`, the symbol products of the
  words of length `K` satisfy `Σ_{|w_i| = K} c_i ∏ sym = 0`.
- `op_xV_mul`, `evalWord_xV_mul`: the operators commute with multiplication by `ξ_q`;
  `eq_zero_of_kills_rename`: a combination of words vanishing on the polynomials in `v` alone
  (`rename vV Q`) vanishes on all of `Pol n`.

## Provenance

Internal infrastructure of Task 7064 for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
