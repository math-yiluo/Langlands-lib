# Formal real polynomials in `v` and `v̄`

A polynomial `P` in the variables `(k, false)` (for `v_k`) and `(k, true)` (for `conj v_k`)
defines the function `evalC P v = P(v, v̄)`.

## Results

- `evalC_add`, `evalC_mul`, `evalC_C`, `evalC_X`.
- `evalC_injective`: if `evalC P` vanishes identically then `P = 0`. Proof: the algebra map
  `realSubst` (`v ↦ x + i y`, `v̄ ↦ x - i y`) is injective (it has the left inverse
  `realSubstInv`), and `realSubst P` vanishes at all real points (`eval_realSubst`), hence is
  zero by `MvPolynomial.funext_set`.
- `hasFDerivAt_evalC`, `fderiv_evalC_apply`: the real derivative of `evalC P` at `v` in the
  direction `w` is `Σ_c evalC (∂_c P) v · coord_c w`; `differentiable_evalC`.
- `wirt φ v w = ½ (Dφ(v)[w] - i Dφ(v)[i w])`, the complex-linear part of the derivative;
  `wirt_evalC`: `wirt (evalC P) v w = Σ_k evalC (∂_{(k, false)} P) v · w_k`.
- `holPart`: the substitution `v ↦ v`, `v̄ ↦ 0` into the polynomials in `v`; `holIncl`: the
  holomorphic polynomials; `holPart_holIncl`, `evalC_holIncl`, and `holPart_pderiv`:
  `holPart (∂_{(k, false)} P) = ∂_k (holPart P)`.

## Provenance

Internal infrastructure for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
