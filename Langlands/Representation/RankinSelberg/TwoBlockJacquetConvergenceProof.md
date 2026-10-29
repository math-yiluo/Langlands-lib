# Ordinary absolute convergence of the two-block Jacquet integral

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof`,
namespace `Langlands.RankinSelberg.TwoBlockConvergence`.

Author: Worker 886.

The module proves

```lean
theorem Langlands.RankinSelberg.twoBlockJacquetConvergence :
    TwoBlockJacquetConvergenceStatement.{uF, uW}
```

for the published closed proposition
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement`
(`Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`).
The statement's Lean/Markdown pair and its imports are unchanged.

## What is proved

The statement covers every `p`-adic field `F` with its canonical structure,
every nontrivial unitary additive character `ψ`, every supplied self-dual Haar
measure `ν`, `t`, `m`, `h : ∑ i, (m i + 1) = t + 1`, carriers `W i`, and blocks
`τ i` with `IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)`. It also
covers every supplied pair `ell i : glInverseFunctionals ψ (m i) (τ i)` with
nonzero values. For all of these there is one real `C` such that for every real
`u > C`, every section `f` of the lower normalized induction of
`twoBlockOppositeTwistBlocks F m τ u` (the blocks `τ_0 |det|^(-u)` and
`τ_1 |det|^u` on the same carriers), and every ambient `g`, the integrand
`TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g` is Mathlib-`Integrable`
for `rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)`. The bound `C` depends only on
`F`, `ψ`, `m`, `τ` and `ell`, not on `u`, `f` or `g`. The hypothesis that the
functionals are nonzero is not used.

## Route and provenance

JPSS 1983 (source ID `jpss-1983-rankin-selberg`), Section 4.6, printed pages
410–411, prove this convergence from finite growth exponents of Whittaker
functions (Section 2.5, printed pages 388–389) and a positive integral
estimate. The implemented proof takes a different, elementary route, and it
assumes no growth, asymptotic, gauge or integrability certificate as a premise:

- No Whittaker model or irreducibility is used. Of `IsOfWhittakerType`, only
  admissibility and finite generation over the group algebra are used (its
  first two components). Of `glInverseFunctionals`, only the
  transformation law under the upper unipotent group is used. Hence reducible
  full-type blocks are covered directly, without passing to source Whittaker
  models or coefficient-image maps.
- The growth exponents are replaced by a geometric bound `C B^e` in the size
  `e` of the group element. It is proved by Hecke operators in the helper
  modules `UnipotentSandwich`, `DominantGrowth` and `FunctionalGrowth`.
- The positive integral estimate is replaced by a geometric-series bound over
  the boxes `{x : ϖ^e x ∈ O}` (helper module `BoxIntegrability`). The size of
  the Iwasawa factor of `u(x)` is controlled in helper module `RadicalIwasawa`.
- The opposite twist contributes the factor `q^(-2ud)` that beats both the
  growth `B^d` and the box volume `q^(abd)` once `u` is large. Here `a = m 0 + 1`
  and `b = m 1 + 1`.

Notation: `T = F.canonicalTopologicalData`, `O` its integers, `ϖ` the
canonical uniformizer (`LocalFactor.PadicAbelian.uniformizerUnit T`), `q` the
residue cardinality, `K₀ = integralOpen F t = GL_(t+1)(O)`.
`IsEntryBounded ϖ e g` means that `ϖ^e g` and `ϖ^e g⁻¹` are integral. All
statements below are in section `Padic` unless noted.

## Section `Character` (any valued field)

`valuation_le_of_mem_levelSet`: elements of `𝔪^a` have valuation at most
`v(ϖ)^a`, for a uniformizing element `ϖ`. A nonzero element of the maximal
ideal has valuation `v(ϖ)^n` with `n > 0`, hence at most `v(ϖ)`. The bound then
passes to `𝔪^(a+1) = 𝔪^a 𝔪` by induction on `a`, with
`Submodule.mul_induction_on` and the ultrametric inequality for sums.

## Section `Functional`

- `uniformizerUnit_isUniformizingElement`: the canonical uniformizer is a
  uniformizing element of the canonical valuation. This is checked through the
  value-group isomorphism with `ℤ` and `uniformizerUnit_zpow_value`.
- `exists_functional_growth`: for `ρ` of Whittaker type for `standardCharacter ψ n`
  and `ℓ ∈ glInverseFunctionals ψ n ρ`, there is `B ≥ 1` such that every `v` has
  a `C` with `‖ℓ(ρ(g) v)‖ ≤ C B^e` for `g` bounded by `e`. Proof: apply
  `FunctionalGrowth.exists_growth` with `χ(z) = ψ(z)⁻¹`. Its hypotheses hold:
  `‖χ‖ = 1`; `χ(x₀) ≠ 1` for some `x₀` because `ψ` is nontrivial; `ϖ^c₀ x₀` is
  integral for some `c₀`; and `χ` is trivial on `𝔪^a₀` for `a₀` from the
  conductor `T.exists_additiveTrivialAt ψ`, using
  `valuation_le_of_mem_levelSet`.

## Section `Tensor`

- `exists_blockTensor_growth`: suppose each block functional satisfies
  `‖ell i (τ i g v)‖ ≤ C B_i^e`. Then for each tensor `w` there is a `C` with
  `‖(⊗ ell i)((⊗ τ i)(b) w)‖ ≤ C (B_0 B_1)^e` for Levi elements `b` whose two
  blocks are bounded by `e`. The proof is by `PiTensorProduct.induction_on`:
  products of the block bounds for pure tensors, and the triangle inequality
  for sums.
- `tensorContraction_blockTensor_twist`: for the opposite twists, the
  contracted block tensor equals `|det b_0|^(-u) |det b_1|^u` times the
  untwisted one. This is computed on pure tensors with
  `twoBlockOppositeTwistBlocks_apply`.

## Section `Sections`

- `finite_image_sectionEval_integralOpen`: a section takes finitely many values
  on `K₀`. It is locally constant (`Induction.eval_isLocallyConstant`) and `K₀`
  is compact.
- `exists_integral_growth`: one constant `C ≥ 0` serves in
  `exists_blockTensor_growth` for all the values `f(k)`, `k ∈ K₀`. Take the sum
  of the finitely many constants.

## Section `Bounds`

- `norm_inv_leviHalfModulus_le_one`: if `|det b_0| = q^d` and
  `|det b_1| = q^(-d)`, then the published `leviModulus` at `b` is
  `(q^d)^(m 1 + 1) (q^d)^(m 0 + 1) ≥ 1` (`leviModulus_apply`). So the inverse half
  modulus has norm at most `1` (`leviHalfModulus_apply`).
- `residue_pow_rpow_neg`: `(q^d)^(-u) = (q^(-u))^d`.
- `norm_integrand_le` (**pointwise bound**): let `u(x) = q' k` with `k ∈ K₀`,
  both diagonal blocks of `q'` bounded by `d`, `|det q'_0| = q^d` and
  `|det q'_1| = q^(-d)`. Suppose also the uniform bound of
  `exists_integral_growth` holds with constants `C` and `Bp`. Then
  `‖integrand ψ ell f 1 x‖ ≤ C (Bp q^(-u) q^(-u))^d`. Proof: `‖ψ‖ = 1`
  (`norm_positiveKernel`). By the published covariance
  `scalarSection_covariant`, the value at `q' k` is the inverse half modulus
  times the contracted block tensor at `k`. The twist factors have norm
  `(q^(-u))^d` each (`tensorContraction_blockTensor_twist`).

## Section `Integrability`

`integrable_integrand_one`: assume the uniform bound on `K₀` with `C ≥ 0`,
`Bp ≥ 0`, and the factorization hypothesis `hfac`. The hypothesis says that every `x`
has `u(x) = q' k` as in `norm_integrand_le`, with `x ∈ box F (m 0 + 1) (m 1 + 1) d`.
Assume also `Bp q^(-u) q^(-u) q^(ab) < 1`. Then `integrand ψ ell f 1` is integrable
for `rectangularMeasure ν a b`. Proof: the integrand is continuous, since it is
locally constant in the section value times the continuous kernel. Apply
`integrable_of_forall_exists_mem_box` with `μ(box e) = μ(O)^(ab) (q^(ab))^e`
(`rectangularMeasure_box`). The box exponent and the pointwise bound for `x`
come from `hfac x` and `norm_integrand_le`.

## Section `Assembly`

`exists_bound_isAbsIntegrable_of_factorization`: given `hfac`, the conclusion
of the target holds with `C = (log_q(B_0 B_1) + ab) / 2`, where the `B_i` come
from `exists_functional_growth`. For `u > C`, a section `f` and `g`, the
published `integrand_inducedRep` rewrites the integrand at `g` as the integrand
at `1` of the translate `ρ(g) f`. `exists_integral_growth` for that translate
gives the constant, and
`B_0 B_1 q^(-2u) q^(ab) = q^(log_q(B_0 B_1) - 2u + ab) < 1`.

## The theorem

`Langlands.RankinSelberg.twoBlockJacquetConvergence`: introduce the telescope
of the statement and apply `exists_bound_isAbsIntegrable_of_factorization` with
`ν.val` and `hfac := exists_radical_factorization F h` from `RadicalIwasawa`.

## Helper modules

All under `Langlands/Representation/RankinSelberg/TwoBlockJacquetConvergence/`,
each with its own Markdown file:

- `UnipotentSandwich`: `ϖ^lam₁ g ϖ^lam₂ = x ϖ^(lam₁+lam₂) y`, with `x` upper
  unipotent, for `g` in a principal level.
- `DominantGrowth`: Hecke-operator growth bound on the antitone cone.
- `FunctionalGrowth`: uniform geometric growth of character functionals for
  admissible, finitely generated representations.
- `BoxIntegrability`: integrability from geometric box bounds, and box
  volumes.
- `RadicalIwasawa`: the controlled lower Iwasawa factorization of `u(x)`.

The proof uses no `sorry` and no new axioms. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.
