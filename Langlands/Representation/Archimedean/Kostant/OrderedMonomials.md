# Ordered monomials in the universal enveloping algebra

The setting is a basis `b` of `L` indexed by a finite type `B`, together with a list `bs` that
enumerates `B` without repetition. For `α : B →₀ ℕ`, the ordered monomial `E^α` is the word in
which each `b c` appears `α c` times, with the indices taken in the order of `bs` (`expand`,
`orderedMonomial`).

* `degreeFiltration_le_orderedSpan` (the spanning half of Poincaré–Birkhoff–Witt): `U_N` is
  spanned by the `E^α` of degree at most `N`. The proof is a strong induction on `N`. A word is a
  combination of words in basis elements, and such a word differs from the ordered monomial of
  its multiset of letters by an element of `U_{N-1}` (Library lemma `word_sub_word_mem_of_perm`).
* `symbol_orderedMonomial`: suppose the symbols send `b c` to the variable `X c` of
  `MvPolynomial B K`. Then `σ_N(E^α) = X^α` if `deg α = N`, and `0` if `deg α < N`.
* `mem_degreeFiltration_of_symbol_eq_zero` (the kernel of the symbol): if `P ∈ U_{N+1}` and
  `σ_{N+1}(P) = 0`, then `P ∈ U_N`. Write `P` in ordered monomials and compare the coefficients
  of the distinct monomials `X^α`.
