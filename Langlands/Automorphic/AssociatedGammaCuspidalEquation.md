# The completed cuspidal pair equation in the comparison-engine format

Supporting module (module `Langlands.Automorphic.AssociatedGammaCuspidalEquation`), glue step G1 of the proof of
`AssociatedGammaStatement`. It specializes `AssociatedGammaCompletedEquation` to the local
factors of a published `FinitePairFactorChoice` (module
`Langlands.Global.Factors.CuspidalPairFactorData`). It also proves the half-plane nonvanishing
of the archimedean pair L-factors that the general conversion needs.

## Archimedean factors (namespace `…FunctionalEquationComparison.CompletedEquationAdapter`)

- `gammaBlock_denominator_ne_zero`: a shifted Gamma block (`GammaBlock.real a` or
  `GammaBlock.complex a`) has no pole on `re s > -re a`. Proof: by `GammaBlock.real_isPole` /
  `GammaBlock.complex_isPole`, a pole is at `s = -a - 2n` resp. `s = -a - n` with `n : ℕ`. Its
  real part is then at most `-re a`.
- `product_denominator_ne_zero`: a finite list product of `ReciprocalEntire` functions, each
  without poles on a right half-plane, has no poles on a right half-plane (induction on the
  list, `ReciprocalEntire.denominator_mul`, maximum of the bounds).
- `gammaProduct_denominator_ne_zero`, `realPairLFactor_denominator_ne_zero`,
  `complexPairLFactor_denominator_ne_zero`: consequences for Gamma products and for the real
  and complex archimedean pair L-factors (`realLFactor_eq_gammaProduct`,
  `complexLFactor_eq_gammaProduct`).
- `prod_inv_denominator_ne_zero`: for a finite family `F i` of `ReciprocalEntire` functions
  whose denominators have no zeros on right half-planes, `∏ i, (F i).denominator s⁻¹ ≠ 0` for
  `re s > ∑ i, |σ i|`.
- `nonzeroMeromorphic_prod_inv_denominator`: that product has nonzero germ everywhere
  (published `nonzeroMeromorphic_denominator`, `NonzeroMeromorphic.inv`, `finsetProd`).
- `nonzeroMeromorphic_of_differentiable_ne_zero`: an entire function without zeros has nonzero
  germ everywhere.

- `archimedeanL_spec`: for two finite families `FR`, `FC` of `ReciprocalEntire` functions
  without poles on right half-planes, `s ↦ (∏ i, (FR i).denominator s⁻¹) ∏ j, (FC j).denominator s⁻¹`
  is nonzero meromorphic and nonzero on a right half-plane.
- `nonzeroMeromorphic_prod_units`: for two finite families of unit-valued functions whose
  values in `ℂ` are entire, the product of all values is nonzero meromorphic.
- `cuspidalInfiniteL_spec`: the archimedean L-factor `infiniteL` of the published
  `CuspidalPairGlobalFunctionalEquationStatement`, the product of the reciprocal denominators of
  `realPairLFactor (dR v) (dR' v)` and `complexPairLFactor (dC v) (dC' v)`, is nonzero
  meromorphic and nonzero on a right half-plane. This holds for all parameter lists.
- `nonzeroMeromorphic_cuspidalInfiniteEpsilon`: the archimedean epsilon factor
  `infiniteEpsilon` of that statement, with the additive components `aR v`, `aC v` and the
  measure constants `sqrt ‖aR v‖`, `‖aC v‖` used there, is nonzero meromorphic (published
  `differentiable_realEpsilon`, `differentiable_complexEpsilon`; the values are units).

## Finite factors

- `eval_spectralPoint_ne_zero`: if `P.coeff 0 = 1` and `q > 1`, then `P(q^(-s)) ≠ 0` on a right
  half-plane. Proof: `P` is nonzero on a ball of radius `δ` around `0`, and
  `‖q^(-s)‖ = q^(-re s) < δ` once `re s > -log_q δ` (`norm_spectralPoint`, `Real.rpow_logb`).
- `meromorphic_inv_eval_spectralPoint`: `s ↦ 1 / P(q^(-s))` is meromorphic for `q > 0`.
- `inv_eval_spectralPoint_spec`: under the hypotheses of the first lemma, `s ↦ 1 / P(q^(-s))` is
  nonzero meromorphic and nonzero on a right half-plane (`nonzeroMeromorphic_of_ne_zero_halfPlane`).

## The finite pair factor choice (namespace `…CuspidalPairFunctionalEquation.FinitePairFactorChoice`)

For a choice `c` with presentations `P`, `P'`, `Pd`, `Pd'`:

- `one_lt_residueCardinality`: `1 < q_v` at every finite place.
- `finiteL_spec`, `finiteDualL_spec`: `c.finiteL v = 1 / P_v(q_v^(-s))` and
  `c.finiteDualL v` are nonzero meromorphic and nonzero on a right half-plane. The constant
  coefficient of the chosen L-polynomials is `1` by `IsLanglandsPairLPolynomial.coeff_zero`,
  applied to the certificate inside `c.lPolynomial_spec v` resp. `c.dualLPolynomial_spec v`.
- `nonzeroMeromorphic_finiteEpsilon`: the epsilon monomial `c_v q_v^(-m_v s)` is nonzero
  meromorphic (published `nonzeroMeromorphic_epsilonMonomial`).
- `finiteEpsilon_eq_one`: if `c.IsUnramifiedOutside S` and `v ∉ S`, then `ε_v = 1`.
- `exists_engineInputs`: let `c` be unramified outside `S`, let `S ⊆ B` be finite sets of
  finite places, and let `Linf`, `Ldinf`, `εinf` be nonzero meromorphic, with `Linf` and
  `Ldinf` nonzero on a common right half-plane. Then
  `c.CompletedEquationHolds S Linf Ldinf εinf` gives `σ'` and partial L-functions `Lp`, `Lpd`
  with `Admissible`, `HasEulerProductsOutside … σ'` and `FunctionalEquation` at
  `univ.disjSum B`. These hold for the `FiniteEulerData` whose local factors are the published
  `lumpedArch w₀ Linf Ldinf εinf` at the infinite places (all archimedean factors at one place
  `w₀`, the constant `1` elsewhere) and `(c.finiteL v, c.finiteDualL v, c.finiteEpsilon v)` at
  the finite places.
  Proof: `functionalEquation_of_completedEquation` with the published
  `lumpedArch_nonzeroMeromorphic` and `lumpedArch_prod_*` lemmas, the three finite-factor
  lemmas above, `finiteEpsilon_eq_one` on `B \ S`, and countability of the finite places
  (`Langlands.Global.finitePlace_countable`).
- `exists_engineInputs_cuspidal`: `exists_engineInputs` for the archimedean factors
  `infiniteL`, `dualInfiniteL`, `infiniteEpsilon` written exactly as in
  `CuspidalPairGlobalFunctionalEquationStatement`, for any parameter lists `dR … dCd'` and
  components `aR`, `aC` on finite index types. The archimedean hypotheses of
  `exists_engineInputs` come from `cuspidalInfiniteL_spec` (for the L-factor and its dual) and
  `nonzeroMeromorphic_cuspidalInfiniteEpsilon`.

The residue-cardinality bound reuses `FinitePairFactorChoice.one_lt_residueCardinality` from [CuspidalPairResidueCardinality](../Global/Factors/CuspidalPairResidueCardinality.md).
