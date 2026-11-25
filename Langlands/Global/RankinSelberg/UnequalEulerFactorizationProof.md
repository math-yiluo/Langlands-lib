# Proof: partial Euler factorization of the unequal-rank global Whittaker integral

Module `Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof`.

The theorem `Langlands.Global.RankinSelbergGlobal.unequalEulerFactorization` proves the
Library statement `Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorizationStatement.{u, uQ}`
(module `Langlands.Global.RankinSelberg.UnequalEulerFactorizationStatement`,
[`UnequalEulerFactorizationStatement`](UnequalEulerFactorizationStatement.md)) unchanged. The
universe parameters are `u` (the number field) and `uQ` (the local factors of the spectral
presentations). The only axioms are `propext`, `Classical.choice` and `Quot.sound`.

The statement: let `ψ` be a nontrivial unitary character of `𝔸` trivial on `F`, and let
`T`, `T'` be actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with `t < r`, with
spectral presentations `P`, `P'`. Let `S` be a finite set of finite places that contains
both exceptional sets and outside which every finite component of `ψ` has conductor `𝒪_v`.
Then there is one `σ` that works for all vectors `x`, `x'` that are `GL(𝒪_v)`-fixed at every
finite `v ∉ S`. For every `s` with `σ < Re s`, the integrand of `Ψ(s; W_x, W'_x')` is
integrable, the unramified pair factors `L(s, Π_v × Π'_v)` (`v ∉ S`) are absolutely summable
around `1` and have a product `p`, and `Ψ(s; W, W') = Ψ_(S∪∞)(s; W, W') · p`.

## The proof

The proof is one term:

```lean
theorem unequalEulerFactorization : UnequalEulerFactorizationStatement.{u, uQ} :=
  unequalEulerFactorizationReduction UnramifiedWhittaker.unramifiedWhittakerFactorization
    whittakerCellDecomposition unequalUnfoldingStatement_proof
```

`unequalEulerFactorizationReduction` proves
`UnequalEulerFactorizationReductionStatement.{u, uQ}`. This statement is the implication

  `UnramifiedWhittakerFactorizationStatement.{u, uQ} → WhittakerCellDecompositionStatement.{u} →
  UnequalUnfoldingStatement.{u} → UnequalEulerFactorizationStatement.{u, uQ}`.

It is in module `Langlands.Global.RankinSelberg.UnequalEulerFactorizationReduction`, which
was ported together with this module ([`UnequalEulerFactorizationReduction`](UnequalEulerFactorizationReduction.md)).
The three premises are discharged by Library theorems:

- (A) `UnramifiedWhittaker.unramifiedWhittakerFactorization :
  UnramifiedWhittakerFactorizationStatement.{u, uQ}` (module
  `UnramifiedWhittakerFactorizationProof`). At a finite place `v ∉ S`, the global
  Whittaker functions of a vector that is spherical outside `S`, for `ψ` and for `ψ⁻¹`, factor
  as `W_x(g ι_v(h)) = W_x(g) W°(h; a)` when `g_v = 1`. Here `W°(·; a)` is the explicit
  spherical Whittaker function.
- (B_v) `whittakerCellDecomposition : WhittakerCellDecompositionStatement.{u}` (module
  `WhittakerCellDecomposition`): the one-place Iwasawa cell decomposition
  `∑_λ N(v)^(∑_(i<j)(λ_i-λ_j)) ∫_(U_S) f(ι_v(ϖ^λ) ·) = ∫_(U_(S∪{v})) f` of the Whittaker
  quotient measure.
- `unequalUnfoldingStatement_proof : UnequalUnfoldingStatement.{u}` (module
  `UnequalUnfoldingProof`). Its first part gives the integrability of the integrand of
  `Ψ(s; W, W')` for `Re s > C`, with `C` depending only on `T` and `T'`.

## What the reduction does

The reduction module and its helper module `UnequalKernelLocalPoint`
([`UnequalKernelLocalPoint`](UnequalKernelLocalPoint.md)) were ported together with this module. Their
Markdown files describe them in detail. In outline:

1. **The half-plane.** `σ = max(C, σ₁, σ₂)`, chosen before the vectors. `C` comes from the
   unfolding statement. `σ₁` comes from `exists_partialEulerFactor_convergence` (convergence
   of the Euler product). `σ₂` comes from the Library's local Cauchy sum
   `RankinSelberg.UnramifiedUnequalLocalSum.exists_hasSum_localTerm`, applied with the Satake
   bounds of `P` and `P'` (`exists_hasSatakeBound_presentation`). The local sum gives a
   half-plane that is uniform in the place `v`.
2. **Integrability and the product** come from `C < Re s` and `σ₁ < Re s`, with
   `p = partialEulerProduct P P' hP hP' s`.
3. **One place at a time.** `setIntegral_insert_eq_mul` shows that for a finite `A ⊇ S` and
   `v ∉ A`, `∫_(U_(A∪{v})) f = L(s, Π_v × Π'_v) · ∫_(U_A) f`, where `f` is the integrand of
   `Ψ(s; W, W')`. By (A), with the uniformizer `placeUniformizer v` of
   `LocalPointFactorization`, `W` and `W'` factor at `v`. By `ordinaryKernel_localPoint_mul`
   (module `UnequalKernelLocalPoint`), `f(ι_v(ϖ^λ) q) = c_λ f(q)` on `U_A`. Then (B_v) and
   `absNorm_zpow_mul_eq_localTerm` turn `∫_(U_(A∪{v})) f` into
   `∑_λ localTerm q_v a b s λ · ∫_(U_A) f`. The local Cauchy sum evaluates
   `∑_λ localTerm q_v a b s λ` as `∏_(i,j) (1 - a_i b_j q_v^(-s))⁻¹`, which equals
   `partialEulerFactor P P' hP hP' v s`.
4. **Passing to the limit.** `integral_eq_hasProd_mul_setIntegral` (module
   `PartialIntegralExhaustion`) turns these one-place steps and `HasProd` into
   `∫ f = p · ∫_(U_S) f`. By `partialUnequalWhittakerIntegral_eq_setIntegral` this is the
   identity `Ψ(s; W, W') = Ψ_(S∪∞)(s; W, W') · p`.

## Provenance

The statement Markdown cites Cogdell 2004, §2.2 (printed p.206), with Theorem 3.3 (printed
p.215). Cogdell factors `Ψ(s; W_φ, W'_φ')` for factorizable cusp forms into local integrals.
He evaluates the unramified local integrals by the Shintani–Casselman–Shalika formula
(Theorem 3.3). The Library's statement keeps the global partial integral `Ψ_(S∪∞)` instead of
a product of local integrals. So this proof adds the unramified places one at a time inside
the global integral. The cell decomposition (B_v) plays the role of the local Iwasawa
integration formula, and the local Cauchy sum plays the role of the
Shintani–Casselman–Shalika evaluation. For the absolute convergence Cogdell refers to gauge
estimates; here it comes from the Library's unfolding proof. The split into the three premises is internal to
the proof of `UnequalEulerFactorizationStatement`.
