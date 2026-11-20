# Reduction of the Whittaker expansion to the standard generic character

Module `Langlands.Global.SmoothWhittakerExpansion.Torus`, namespace
`Langlands.Global.SmoothWhittakerExpansion`. Helper module for the proof of
`Langlands.Global.WhittakerExpansionStatement` (Task 5713). It carries out step 2 of that
task's proof guide: the Whittaker expansion for the generic character with simple-root
coefficients `m = (m_0, …, m_{r-1})` reduces to the standard coefficients `m = 1`, which is the
case treated by the Library's Whittaker expansion core
(`Langlands.Global.RankinSelberg.WhittakerExpansionCore`). Everything is proved; the axioms
are `propext`, `Classical.choice` and `Quot.sound`.

Notation. `F` is a number field, `Points F n = GL_n(𝔸)` (the adelic points of the general linear
group scheme), `N_n(𝔸) = unipotentAdelic F n`, `N_n(F)` its rational subgroup, and
`W_{ψ,m} f = generalLinearWhittakerFunction F r ψ m f`, the integral of
`f(n g) conj(ψ(Σ_i m_i n_{i,i+1}))` over `N_{r+1}(F) \ N_{r+1}(𝔸)` against the normalized
quotient measure `normalizedRationalQuotientHaarMeasure`.

## Provenance

The reduction is the one recorded in the Markdown of the target statement
`Langlands.Global.GeneralLinearWhittakerExpansionStatement` (section "The character"): with
`t = diag(t_0, …, t_{r-1}, 1)` rational and `t_i / t_{i+1} = m_i`, the substitution
`n ↦ t n t⁻¹` on `N(F) \ N(𝔸)` gives `W_{ψ,m}(g) = W_{ψ,1}(t g)`, and `γ ↦ t' γ` permutes
`N_r(F) \ GL_r(F)`. It is the standard argument behind the remark that the Whittaker expansion
(Getz–Hahn, Theorem 11.3.6, p.298; Cogdell 2004, Theorem 1.1, p.200) holds for every generic
character once it holds for the standard one. The Lean statements and proofs are this module's
own. The measure-preservation argument follows the Library's proof of
`measurePreserving_dualConjUnipotent` (module `Langlands.Global.RankinSelberg.UnfoldingDualGL`).

## Section `Weights`

- `torusWeight m k = ∏_{j < r, k ≤ j} m_j` for `k ∈ Fin (r + 1)`. It is nonzero when every
  `m_j` is (`torusWeight_ne_zero`), equals `1` at `k = r` (`torusWeight_last`), and satisfies
  `e_i = m_i · e_{i+1}` for `i < r` (`torusWeight_castSucc`), i.e. `e_i / e_{i+1} = m_i`.
- `torusUnit hm k` is `e_k` as a unit of `𝔸`.
- `torusLevi hm = t' = diag(e_0, …, e_{r-1}) ∈ GL_r(F)` and
  `torusPoint hm = t = diag(t', 1) = cornerAdelicPoint F r t'`.
- `matrixOf_torusPoint`: the adelic matrix of `t` is `diag(e_0, …, e_{r-1}, e_r = 1)`. Proof:
  entrywise, from the Library's `cornerEmbedding_apply`.

## Section `Conjugation`

- `torusPoint_eq_rational`, `torusPoint_mem_rationalSubgroup`: `t` is a rational point.
- `torusConj hm : N_{r+1}(𝔸) ≃ₜ* N_{r+1}(𝔸)` is `n ↦ t n t⁻¹`, the Library's
  `QuotientIntegration.subgroupAutomorphism` of `conjugation t`; it preserves `N_{r+1}(𝔸)`
  because `t` is diagonal (`conj_mem_iff_of_diagonal`). `coe_torusConj` and
  `coe_torusConj_symm` give its values.
- `mem_rationalSubgroup_of_rational`: a rational point lying in `N_n(𝔸)` lies in `N_n(F)`
  (Library `mem_unipotentRationalImage_iff_mem_inf` and `mem_unipotentRationalImage_iff`).
  Hence `torusConj` and its inverse preserve `N_{r+1}(F)` (`torusConj_mem`,
  `torusConj_symm_mem`, `torusConj_mem_iff`).
- `genericCharacter_torusConj`: `ψ_1(t n t⁻¹) = ψ_m(n)`. The `(i, i+1)` entry of `t n t⁻¹` is
  `e_i n_{i,i+1} e_{i+1}⁻¹ = m_i n_{i,i+1}` (Library `matrixOf_conj_apply`).

## Section `Measure`

Here `φ` is any continuous automorphism of `N_n(𝔸)` with `φ x ∈ N_n(F) ↔ x ∈ N_n(F)`.

- `symm_mem_iff`: `φ⁻¹` has the same property.
- `existsUnique_mem_preimage_fundamentalDomain`, `isFundamentalDomain_preimage`: the preimage
  under `φ` of the Library's chosen Borel fundamental domain `D` of `N_n(F)` in `N_n(𝔸)` is
  again a fundamental domain.
- `measurePreserving_haar_of_rational`: `φ` preserves Haar measure. The image of Haar measure is
  `c · Haar` (`Measure.isMulLeftInvariant_eq_smul`); evaluating on `D` and using that `φ⁻¹(D)`
  and `D` are fundamental domains of the same finite positive mass
  (`haar_unipotentFundamentalDomain`, compactness of `N_n(F) \ N_n(𝔸)`) gives `c = 1`.
- `quotientMap φ hφ` is the induced measurable equivalence of `N_n(F) \ N_n(𝔸)` (the Library's
  `QuotientIntegration.quotientAutomorphism`, as a measurable equivalence of Borel spaces);
  `quotientMap_mk`: `N_n(F) x ↦ N_n(F) φ(x)`.
- `measurePreserving_quotientMap`: it preserves `normalizedRationalQuotientHaarMeasure`. That
  measure is a scalar multiple of the push-forward of Haar restricted to `D`. Pushing forward by
  the induced map is pushing forward Haar restricted to `φ(D) = φ⁻¹⁻¹(D)` (by
  `measurePreserving_haar_of_rational` and `MeasurableEmbedding.restrict_map`), and the quotient
  measure does not depend on the fundamental domain (`LeftCosetSpace.quotientMeasure_eq`).

## Section `Whittaker`

- `generalLinearWhittakerFunction_eq_torus`: for `ψ` trivial on `F` and `f` left invariant
  under `GL_{r+1}(F)` (no measurability is assumed),
  `W_{ψ,m} f (g) = W_{ψ,1} f (t g)`. Proof: by `measurePreserving_quotientMap` for `torusConj`
  (`MeasurePreserving.integral_comp'` for a measurable equivalence), the integral defining
  `W_{ψ,1} f (t g)` equals the integral of its integrand composed with the induced map. At a
  class with representative `n`, the representative of the image class is `l · t n t⁻¹` with
  `l ∈ N_{r+1}(F)` (`exists_out_mk_eq`). Then `f(l t n t⁻¹ t g) = f(n g)` by left invariance
  under the rational points `l` and `t`, and `ψ_1(l t n t⁻¹) = ψ_1(l) ψ_m(n) = ψ_m(n)`
  (`genericCharacter_mul`, `genericCharacter_rational`, `genericCharacter_torusConj`). So the
  integrands agree pointwise with the integrand of `W_{ψ,m} f (g)`.
- `conj_mem_upperUnipotent_of_diagonal`, `torusLevi_conj_mem`, `torusLevi_inv_conj_mem`:
  conjugation by `t'` or `t'⁻¹` preserves the upper unitriangular matrices.
- `cosetEquiv hm`: the permutation `N_r(F) γ ↦ N_r(F) t' γ` of `N_r(F) \ GL_r(F)`
  (`UnipotentRationalCosets F r`), well defined and bijective because `t'` normalizes `N_r(F)`
  (`Quotient.congr` with left multiplication by `t'`). `cosetEquiv_apply`: the image of `q` is
  the class of `t' · q.out`.
- `cornerAdelicPoint_mul`: `diag(a b, 1) = diag(a, 1) diag(b, 1)`.
- **`exists_cosetEquiv_genericCharacter`** (main result). Let `ψ` be a standard additive
  character (`IsStandardAdditiveCharacter`: continuous, nontrivial, trivial on `F`, unitary)
  and `m_i ≠ 0` for all `i`. There is a permutation `σ` of `N_r(F) \ GL_r(F)` such that for
  every `f : GL_{r+1}(𝔸) → ℂ` left invariant under `GL_{r+1}(F)`, every coset `q` and every `g`,
  `W_{ψ,m} f (diag(q.out, 1) g) = W_{ψ,1} f (diag((σ q).out, 1) g)`. Take `σ = cosetEquiv hm`.
  By `generalLinearWhittakerFunction_eq_torus` the left side is
  `W_{ψ,1} f (t diag(q.out, 1) g) = W_{ψ,1} f (diag(t' q.out, 1) g)`. Since `(σ q).out` and
  `t' q.out` lie in the same coset of `N_r(F)`, the Library's
  `whittaker_padRational_of_rightRel` (with `padRational_eq_cornerAdelicPoint`) identifies this
  with the right side.

## Scope

The module proves only the reduction. It does not prove the Whittaker expansion itself, nor
the unitarity of continuous characters of `𝔸 / F` needed to obtain
`IsStandardAdditiveCharacter` from the hypotheses of the target statement.
