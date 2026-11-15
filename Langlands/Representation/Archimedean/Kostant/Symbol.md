# Symbols in the universal enveloping algebra through derivations

`SymbolData K L R S` consists of a Lie algebra map `ρ : L → End_K(R)` whose values are
derivations of the commutative algebra `R`, an ideal `𝔪` of `R`, an algebra map `ε : R → S` that
vanishes on `𝔪`, and an element `l ∈ 𝔪`. The degree-`N` symbol of `P ∈ U(L)` is
`σ_N(P) = ε(ρ(P) lᴺ) / N!`, where `ρ(P)` is the action of `P` through the universal property.

The key computation, `IsLeibniz.prod_apply_pow_sub_mem`, is an induction on the number of
derivations. If `M ≤ N` derivations `D₁, …, D_M` are applied to `fᴺ` with `f ∈ 𝔪`, the result is
`N!/(N-M)! · f^{N-M} · ∏ D_t f` modulo `𝔪^{N-M+1}`. The induction uses `D(𝔪^{k+1}) ⊆ 𝔪^k`.
Applying `ε` gives the following.

* `symbol_word_of_length_eq`, `symbol_word_of_length_lt`: a word `x₁ ⋯ x_N` has symbol
  `∏ ξ(x_t)`, where `ξ(x) = ε(ρ(x) l)`; a shorter word has symbol `0`.
* `symbol_eq_zero_of_mem`: `σ_N` vanishes on `U_M` for `M < N`. Here `U_M` is the Library's
  `degreeFiltration`, which is spanned by words of length at most `M`
  (`degreeFiltration_le_wordSpan`).
* `symbol_mul`: `σ_{a+b}(PQ) = σ_a(P) σ_b(Q)` for `P ∈ U_a`, `Q ∈ U_b`.
* `symbol_commutator`: `σ_N(xP - Px) = δ(σ_N P)` for `P ∈ U_N`, for every derivation `δ` of `S`
  with `δ(ξ y) = ξ⁅x, y⁆`. The proof is an induction on words, with the commutator expanded
  generator by generator.
