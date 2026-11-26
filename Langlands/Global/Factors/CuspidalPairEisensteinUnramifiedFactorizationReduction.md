# The unramified factorization from the local open-cell sum

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnramifiedFactorizationReduction`.

## Content

- `CuspidalPairEisensteinUnramifiedFactorizationReductionStatement.{u,uQ}`, in namespace
  `Langlands.Global`, is the proposition

  ```text
  Shahidi.UnramifiedOpenCellSumStatement.{u} →
    CuspidalPairEisensteinUnramifiedFactorizationStatement.{u,uQ}
  ```

  The premise is the local two-block open-cell sum
  ([UnramifiedOpenCellSumStatement.md](../../Representation/Shahidi/UnramifiedOpenCellSumStatement.md));
  the conclusion is the unramified factorization
  `L^S(1 + s, π × π') · I(φ, s) = I_S(φ, s)`
  ([CuspidalPairEisensteinUnramifiedFactorizationStatement.md](CuspidalPairEisensteinUnramifiedFactorizationStatement.md)).
- `cuspidalPairEisensteinUnramifiedFactorizationReduction` proves it.
- Auxiliary results in namespace `Langlands.Global.CuspidalPairEisenstein.Oneplace`:
  `map_ofTuple`, `Langlands.Global.RankinSelbergGlobal.EqualEulerLocal.mem_ofTuple` (tuples and their spectra);
  `partialEulerFactor_inv_eq`: with a Satake tuple `a` of `P` and a tuple `c` of the
  presentation `Pd` of the contragredient realization at `v`, the spectrum of `P'` at `v` is
  that of the tuple `c⁻¹`, and the inverse of the local pair Euler factor is
  `∏_(i,j) (1 - a_i c_j⁻¹ q_v^(-w))`; `norm_lt_one_of_bounds`, `prod_ne_zero_of_bounds` (this
  product does not vanish for `Re s` large); `openCellHaar_isAddLeftInvariant`.

The module is a reduction: it does not prove `Shahidi.UnramifiedOpenCellSumStatement`, and so
it does not by itself prove `CuspidalPairEisensteinUnramifiedFactorizationStatement`.

## Proof

Fix the data of the conclusion and a section `φ` built from cusp forms spherical outside `S`.

1. **Bounds.** The Library theorem `RankinSelbergGlobal.exists_hasSatakeBound_presentation`
   bounds the Satake parameters of `P` and `P'` outside their exceptional sets by `q_v^(A₀)`
   and `q_v^(B₀)`. The local sum statement for `r`, `t`, `A₀`, `B₀` gives `σ_A`; the Library
   theorem `RankinSelbergGlobal.exists_partialEulerFactor_convergence` gives `σ_E` such that the
   local factors `L_v(w)` of `L^S` satisfy `∑_v ‖L_v(w) − 1‖ < ∞` and `∏_v L_v(w) = L^S(w)` for
   `σ_E < Re w`. The half-plane of the conclusion is
   `max(σ_A, σ_E − 1, A₀ + B₀) < Re s`.
2. **Local data.** At `v ∉ S`, choose tuples `a`, `c` with the spectra of `P` and `Pd`. The
   realization `dualRealization T'` is a contragredient of `T'`
   (`Automorphic.cuspidalContragredientExistence`), so by the Library theorem
   `Automorphic.CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf` the
   spectrum of `Pd` at `v` is the inverse of that of `P'`. Hence `‖c_j⁻¹‖ ≤ q_v^(B₀)`, and
   `L_v(1 + s)⁻¹ = ∏_(i,j) (1 − a_i c_j⁻¹ q_v^(−1−s)) =: E_v`, which is nonzero for
   `A₀ + B₀ < Re s`.
3. **The product of the local sums.** Eventually `‖L_v − 1‖ ≤ 1/2`, and then
   `‖L_v⁻¹ − 1‖ ≤ 2 ‖L_v − 1‖` (`CuspidalPairEulerConvergence.norm_inv_sub_one_le`), so
   `∑_v ‖E_v − 1‖ < ∞` and `∏_v E_v = p` for some `p`
   (`CuspidalPairEulerConvergence.hasProd_of_summable_norm_sub_one`). Multiplying the two
   products, `∏_v L_v E_v = L^S(1 + s) · p`, and `L_v E_v = 1`, so `L^S(1 + s) · p = 1`.
4. **One place.** For finite `A ⊇ S` and `v ∉ A`, the local sum statement at
   `K = CompletionPadic.padicField v`, with the canonical component `ψ_v` of conductor `𝒪_v`
   (`FiniteAdditiveSupport`), the uniformizer
   `RankinSelbergGlobal.LocalPointFactorization.placeUniformizer v`, the tuples `a`, `c` and
   the section `f_v = Shahidi.UnramifiedSection.sectionFunction`, whose transformation law is
   `sectionFunction_law`, gives
   `∑_(y ∈ M(F_v)/M(𝒪_v)) f_v(w u'(y)) conj(ψ_v(y_(t,0))) = E_v`. By
   `openCellIntegrand_localMatrix_add`
   ([CuspidalPairEisensteinOneplaceIntegrand.md](CuspidalPairEisensteinOneplaceIntegrand.md)),
   the integrand at `y_v + Z`, for `Z` integral outside `A`, is that summand times the
   integrand at `Z`. The one-place step `setIntegral_cons_eq_mul`
   ([CuspidalPairEisensteinOpenCellExhaustion.md](CuspidalPairEisensteinOpenCellExhaustion.md))
   gives `I_(A ∪ {v}) = E_v · I_A`, using the integrability hypothesis.
5. **Exhaustion.** `integral_eq_hasProd_mul_setIntegral` gives `I(φ, s) = p · I_S(φ, s)`, hence
   `L^S(1 + s) · I(φ, s) = L^S(1 + s) · p · I_S(φ, s) = I_S(φ, s)`.

## Provenance

The argument is the unramified half of the proof of Shahidi (1981), Theorem 5.1,
pp. 351–352 (`shahidi-1981-certain-l`): the Fourier coefficient of a factorizable section is a
product of local coefficients, and at the unramified places the local coefficient is
`L(1 + s, π_v × π'_v)⁻¹` by Casselman–Shalika (1980), Theorem 5.4
(`casselman-shalika-1980-whittaker`). Here the local factor at each place is supplied by the
local sum statement, and the product over the places is taken by exhausting `M(𝔸)` with the
sets of matrices integral outside finite sets of places. The splitting into the local sum
statement and this reduction is internal.
