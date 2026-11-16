# The equal-rank Whittaker integrand: any representative, and integrability

Module `Langlands.Global.RankinSelberg.EqualEulerIntegrand`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualEulerIntegrand`.

## Purpose and provenance

These are internal auxiliary lemmas for the proof of
`Langlands.Global.RankinSelbergGlobal.EqualEulerFactorizationStatement` (Cogdell 2004, §2.3,
printed p.210, with Theorem 3.3, printed p.215). They introduce no definitions and no
assertions beyond what is proved here, and they assume nothing except the Library statement
`EqualUnfoldingStatement`, which the last two results take as an explicit hypothesis.

Throughout, `n = r + 1`, `N_n(𝔸)` is the upper unipotent subgroup of `GL_n(𝔸)`
(`unipotentAdelic F n`), and `ψ` is a standard additive character of `𝔸`
(`IsStandardAdditiveCharacter F ψ`: continuous, nontrivial, trivial on `F`, unitary).

The Library defines the integrand of the equal-rank Whittaker integral
`Ψ(s; W, W', Φ) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W(g) W'(g) Φ(e_n g) |det g|^s dg` on the quotient
`N_n(𝔸) \ GL_n(𝔸)` by evaluating at the chosen representative `q.out` of each class `q`
(`equalWhittakerIntegrand`, module `EqualIntegrals`). The first two lemmas show that for the
Whittaker functions of cusp forms the value does not depend on that choice. This is the
standard remark that the integrand is left `N_n(𝔸)`-invariant because the generic characters
of `W` and `W'` cancel (Cogdell 2004, §2.3, p.210). The proof of the Euler factorization needs
it to evaluate the integrand at translates `g · ι_v(t)` by local torus elements, which are not
the chosen representatives of their classes.

## Results

- `lastRow_unipotent_mul (u : N_n(𝔸)) (g)`: `lastRow F r (u * g) = lastRow F r g`, that is,
  `e_n (u g) = e_n g`. The last row of a unitriangular matrix is `e_n`. The proof uses
  `Unfolding.isUnitriangular_of_mem_unipotentAdelic` and expands the matrix product.

- `equalWhittakerIntegrand_mk`: for cuspidal realizations `T`, `T'` of `GL_n`, a standard
  `ψ`, vectors `x`, `x'`, any `Φ`, any `s` and any `g ∈ GL_n(𝔸)`, with
  `W = cuspWhittaker F T ψ x` and `W' = cuspWhittaker F T' ψ⁻¹ x'`,

  `equalWhittakerIntegrand F W W' Φ s (N_n(𝔸) g) = W(g) W'(g) Φ(e_n g) |det g|^s`.

  Proof: write the chosen representative as `u g` with `u ∈ N_n(𝔸)`
  (`Unfolding.exists_out_mk_eq`). Then `W(u g) = θ_ψ(u) W(g)` and
  `W'(u g) = θ_(ψ⁻¹)(u) W'(g)` (`Unfolding.cuspWhittaker_mul_left`, using that `ψ⁻¹` is
  standard, `Unfolding.isStandardAdditiveCharacter_inv`). Also `θ_(ψ⁻¹)(u) = θ_ψ(u)⁻¹`
  (`Unfolding.genericCharacter_inv_eq_inv`) and `θ_ψ(u) ≠ 0`
  (`Unfolding.genericCharacter_ne_zero`), so the two characters cancel. The last row is
  unchanged (`lastRow_unipotent_mul`) and `|det(u g)| = |det g|`
  (`Unfolding.detPower_unipotent_mul`).

- `exists_integrable_equalWhittakerIntegrand (hU : EqualUnfoldingStatement)`: for every number
  field `F` with compact `F \ 𝔸` and all cuspidal realizations `T`, `T'` of `GL_n`, there is
  `C : ℝ` such that for every standard `ψ`, all `x`, `x'`, every `Φ ∈ S(𝔸^n)` and every
  `s` with `C < Re s`, the integrand `equalWhittakerIntegrand F W W' Φ s` above is integrable
  for `whittakerQuotientMeasure F n`. The constant depends only on `T`, `T'` (not on `ψ`, the
  vectors or `Φ`). Proof: an irreducible realization has a central character
  (`Automorphic.OperatorRealization.irreducibleCentralCharacter`). Apply `hU` to these central
  characters `ω`, `ω'` and take the integrability conjunct of its right half-plane clause.

- `exists_integrable_equalWhittakerIntegrand_unitary (hU)`: the same for a nontrivial unitary
  character `ψ` of `𝔸` trivial on `F`, with `W = cuspWhittaker F T ψ.complex x` and
  `W' = cuspWhittaker F T' ψ.complex⁻¹ x'`. This is the form of the integrability clause of
  `EqualEulerFactorizationStatement`. Proof: `isStandardAdditiveCharacter_of_unitary`
  (module `EqualDualEulerFactorizationReduction`) and the previous result.

## Scope

The integrability results are conditional on `EqualUnfoldingStatement` (Cogdell 2004, §2.3,
pp.210–211), which is a Library statement whose proof is a separate task. They do not prove
convergence of the Whittaker integral independently.
