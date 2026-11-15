# Matumoto's lemma for `∏ᵢ 𝔤𝔩_{n i}(ℂ)`

Source: H. Matumoto, *Whittaker vectors and associated varieties*, Invent. Math. 89 (1987),
Theorem 1 (pp. 220–221), applied to the grading of `𝔤 = ∏ᵢ 𝔤𝔩_{n i}(ℂ)` with
`deg E⟨i,p,q⟩ = q - p` and `s = 1`. The Lean proof follows Matumoto's argument with two changes.
The decomposition (7) by Poincaré–Birkhoff–Witt is replaced by the spanning statement of
`OrderedMonomials`. The `D`-homogeneous component of an annihilating element is extracted by
Lagrange interpolation in `D`.

## Setting

* `π : GLProd ℂ n →ₗ⁅ℂ⁆ Module.End ℂ V` is a representation and `a i p` are complex numbers.
* `whitChar n a X = ∑ i ∑ p ∑ q, if q = p + 1 then a i p * X i p q else 0` is the character `η`.
* `IsWhittaker n π a ℓ` means `ℓ(π(X) v) = η(X) ℓ(v)` for every blockwise strictly upper
  triangular `X` and every `v`. This is exactly the hypothesis of
  `GLProductWhittakerMaximallyFaithfulStatement`.
* `whitPoint n a` is the point with coordinate `a i p` at `⟨i, p, p+1⟩` and `0` elsewhere.

## Main result

`eval_symbol_eq_zero` (Matumoto's lemma) assumes that `ℓ ≠ 0` is Whittaker, that `P ∈ U_N`,
and that `P` acts by `0`. It concludes that the degree-`N` symbol `σ_N(P)` (from
`Center.glSymbol`) vanishes at `whitPoint n a`.

## Proof

1. *Grading.* `hdiag` is the diagonal tuple with entries `-p`, and `gradDer = ad(ι hdiag)`.
   `lie_hdiag_unit` gives `⁅hdiag, E⟨i,p,q⟩⁆ = (q - p) E⟨i,p,q⟩`, so `gradDer` multiplies a
   word in the basis by the sum of the degrees of its letters (`gradDer_word`). `gradDer`
   preserves the annihilator, and so does every polynomial in `gradDer`
   (`envelopingAction_aeval_gradDer`).
2. *Ordered monomials.* `sortedCoords` enumerates the coordinates in decreasing degree
   (`List.mergeSort`). By `degreeFiltration_le_orderedSpan`,
   `P = ∑_α c_α E^α` with `deg α ≤ N`.
3. *Projection.* The Lagrange polynomial `lag` equals `1` at `N` and `0` at the other degrees
   that occur. So `P_N = lag(gradDer) P` is the sum of the terms of weighted degree exactly `N`,
   and `P_N` still acts by `0`.
4. *Words of degree `N`* (`whittaker_word`). Let `l` be a decreasingly ordered list of length at
   most `N` whose degrees add up to `N`.
   * If every letter has degree `1`, the letters are strictly upper triangular units, and
     peeling them off gives `ℓ(l · v) = ∏ ψ(c) ℓ(v) = ψ(σ_N(l)) ℓ(v)`
     (`whittaker_word_of_deg_one`).
   * Otherwise the first letter has degree at least `2`: letters of degree at most `1` cannot
     reach total degree `N` with at most `N` letters unless all have degree `1`
     (`all_eq_one_of_sum`). That first letter is strictly upper triangular with `η = 0`, so
     `ℓ(l · v) = 0`. Also `ψ(σ_N(l)) = 0`, because some letter has `ψ = 0`, or because the word
     is shorter than `N`.
5. *Other degrees.* A word whose degree differs from `N` has `ψ(σ_N(l)) = 0`
   (`eval_symbol_word_eq_zero`). Hence `ψ(σ_N(P)) = ψ(σ_N(P_N))`.
6. Combining these, `ψ(σ_N(P)) ℓ(v) = ℓ(P_N v) = 0`. Taking `v` with `ℓ(v) ≠ 0` proves the claim.
