# Reduction of the unequal-rank partial Euler factorization

Module `Langlands.Global.RankinSelberg.UnequalEulerFactorizationReduction`. Author:
Worker 95.

## 1. Content

The module proves that the published statement
`Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorizationStatement.{u, uQ}`
([`UnequalEulerFactorizationStatement`](UnequalEulerFactorizationStatement.md)) follows from
three Prop-valued statements:

* (A) `UnramifiedWhittakerFactorizationStatement.{u, uQ}` (module
  `Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationStatement`): at a finite
  place `v ∉ S`, the global Whittaker functions `W_x` (for `ψ`) and `W_x` (for `ψ⁻¹`) of a
  vector spherical outside `S` factor as `W_x(g ι_v(h)) = W_x(g) W°(h; a)` for `g_v = 1`.
  Here `W°(·; a)` is the explicit spherical Whittaker function of the standard (resp.
  inverse standard) character of `ψ_v`, and `a` is a tuple enumerating the Satake parameter
  of the presentation at `v`.
* (B_v) `WhittakerCellDecompositionStatement.{u}` (module
  `Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement`): the one-place
  Iwasawa cell decomposition of the Whittaker quotient measure. For integrable `f` on
  `N_m(𝔸) \ GL_m(𝔸)`, a finite set `S`, a finite place `v ∉ S` and a uniformizer `ϖ`,
  `∑_λ N(v)^(∑_(i<j)(λ_i - λ_j)) ∫_(U_S) f(ι_v(ϖ^λ) q) = ∫_(U_(S∪{v})) f`, where `U_S` is
  `unipotentIntegralClasses F m S`.
* `UnequalUnfoldingStatement.{u}` (published): its first part gives, for `Re s > C` with
  `C` depending only on `T` and `T'`, the integrability of the integrand of `Ψ(s; W, W')`.

The module contains, in the namespace
`Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorization`, the helper lemmas of
Section 3 and the theorem `unequalEulerFactorization_of_premises (hA hB hU)`. In the
namespace `Langlands.Global.RankinSelbergGlobal` it contains:

* the definition `UnequalEulerFactorizationReductionStatement.{u, uQ} : Prop`, which is
  the implication (A) → (B_v) → `UnequalUnfoldingStatement` →
  `UnequalEulerFactorizationStatement`;
* the theorem `unequalEulerFactorizationReduction`, which proves it.

This module is a reduction: by itself it does not prove `UnequalEulerFactorizationStatement`.
The module `Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof`
([`UnequalEulerFactorizationProof`](UnequalEulerFactorizationProof.md)) applies
`unequalEulerFactorizationReduction` to the published proofs of (A), (B_v) and
`UnequalUnfoldingStatement`. It is an intermediate result of Task 7022.

## 2. Other inputs

The proof also uses the following published results:

* `exists_partialEulerFactor_convergence` (module `PartialEulerProductConvergence`): there
  is `σ₁` with `∑_(v ∉ S) ‖L_v(s) - 1‖ < ∞` and
  `HasProd L_v (partialEulerProduct P P' hP hP' s)` for `Re s > σ₁`.
* `exists_hasSatakeBound_presentation` (same module): the Satake parameters of a
  presentation satisfy `‖α‖ ≤ q_v^A` for a constant `A` and all `v` outside the exceptional
  set.
* `RankinSelberg.UnramifiedUnequalLocalSum.exists_hasSum_localTerm` (module
  `Langlands.Representation.RankinSelberg.UnramifiedUnequalLocalSum`): for bounds `A`, `B`
  there is `σ₂` such that for every `q > 1`, all tuples `a`, `b` with `‖a_i‖ ≤ q^A`,
  `‖b_j‖ ≤ q^B`, and `Re s > σ₂`, the local terms `localTerm q a b s λ` (`λ ∈ ℤ^(t+1)`) sum to
  `∏_(i,j) (1 - a_i b_j q^(-s))⁻¹`. `localTerm_eq_sphericalWhittaker` expresses a local term
  through the spherical Whittaker functions at torus points.
* `integral_eq_hasProd_mul_setIntegral` (module `PartialIntegralExhaustion`): if
  `HasProd c p` over the finite places outside `S` and adding a place `v ∉ A` to any finite
  `A ⊇ S` multiplies `∫_(U_A) f` by `c_v`, then `∫ f = p · ∫_(U_S) f`.
* `Unfolding.ordinaryKernel_whittaker_unipotent_mul` (module `UnfoldingOrdinary`): the
  kernel `W(diag(g, 1)) W'(g) |det g|^(s-(r-t)/2)` is left `N_(t+1)(𝔸)`-invariant.
* `ordinaryKernel_localPoint_mul` (module `UnequalKernelLocalPoint`, by the same author):
  the pointwise factorization of the kernel under left translation by `ι_v(d)`.
* From `LocalPointFactorization` (Worker 5130): the uniformizer
  `placeUniformizer v`, which is a uniformizer both for `Valued.v`
  (`isUniformizingElement_valued`, as (B_v) needs) and for the canonical valuation of
  `F_v` (`isUniformizingElement_canonical`, as (A) needs); `valued_isEquiv_canonical` with
  `integer_eq_of_isEquiv`; `detNorm_localPoint` and `log_norm_det_torus`.
* `isStandardAdditiveCharacter_of_unitary` (module `EqualDualEulerFactorizationReduction`):
  `ψ.complex` is a standard additive character.
* `GeneralLinear.Spherical.sphericalWhittaker_mul_integral` and `sphericalWhittaker_one`:
  `W°(·; a)` is right `GL(𝒪_v)`-invariant with `W°(1; a) = 1` for integrally trivial
  characters.

## 3. Helper lemmas

* `modulusExponent_eq`: `∑_(i<j) (λ_i - λ_j) = ∑_i (t - 2i) λ_i` for `λ ∈ ℤ^(t+1)`, by
  exchanging the order of summation (`Fin.card_Ioi`, `Fin.card_Iio`).
* `padGL_torus`: `diag(ϖ^λ, 1_(r-t)) = ϖ^(λ, 0)` (`padZeroWeight`), entrywise.
* `mem_integralSubgroup_of_mem_localIntegral`: `GL_m(𝒪_v)` (integral entries for
  `Valued.v`) lies in the integral subgroup of the canonical valuation, since the two
  valuations are equivalent and have the same ring of integers.
* `isIntegrallyTrivial_standardCharacters`: if `ψ_v` has additive conductor `0`, then the
  standard character of `ψ_v` and its inverse are trivial on the integral unitriangular
  matrices (`hasIntegerConductor_of_additiveConductor_eq_zero` and
  `isIntegrallyTrivial_standardCharacter`, `isIntegrallyTrivial_inverseStandardCharacter`).
* `absNorm_zpow_mul_eq_localTerm`: with `ϖ = placeUniformizer v`,
  `N(v)^(∑_(i<j)(λ_i-λ_j)) · W°(diag(ϖ^λ, 1); a) W°(ϖ^λ; b) |det ι_v(ϖ^λ)|^(s-(r-t)/2)` equals
  `localTerm q_v a b s λ`. The proof rewrites with `localTerm_eq_sphericalWhittaker`,
  `padGL_torus`, `modulusExponent_eq`, `detNorm_localPoint` and `log_norm_det_torus`, and
  uses `q_v = N(v)` (`CuspidalPairEulerConvergence.residueCardinality_eq_absNorm`).
* `exists_out_mk_eq`: the chosen representative of the class of `g` in `N(𝔸) \ GL(𝔸)` is
  `n g` with `n ∈ N(𝔸)`.
* **`setIntegral_insert_eq_mul`** (one-place step). Let the kernel be left
  `N_(t+1)(𝔸)`-invariant and the integrand `f` of `Ψ(s; W, W')` integrable. Let `v ∉ A`, and
  let `W`, `W'` factor at `v` through `W°(·; a)`, `W°(·; b)` of integrally trivial
  characters. If `HasSum (localTerm q_v a b s) L`, then
  `∫_(U_(A∪{v})) f = L · ∫_(U_A) f`.

  *Proof.* Put `ϖ = placeUniformizer v`. For `q ∈ U_A` the `v`-component of `q.out` lies in
  `N(F_v) GL(𝒪_v)`. By `exists_out_mk_eq` and the left invariance of the kernel,
  `f(ι_v(ϖ^λ) q) = K(ι_v(ϖ^λ) q.out)`. Torus elements normalize the unitriangular group
  (`isUnitriangular_torus_conj`), so `ordinaryKernel_localPoint_mul` gives
  `f(ι_v(ϖ^λ) q) = c_λ f(q)` on `U_A`, with
  `c_λ = W°(diag(ϖ^λ, 1); a) W°(ϖ^λ; b) |det ι_v(ϖ^λ)|^(s-(r-t)/2)`. Hence the `λ`-th term of
  (B_v) is `N(v)^(∑_(i<j)(λ_i-λ_j)) c_λ ∫_(U_A) f`, which is
  `localTerm q_v a b s λ · ∫_(U_A) f` by `absNorm_zpow_mul_eq_localTerm`. (B_v) says these
  terms sum to `∫_(U_(A∪{v})) f`. They also sum to `L · ∫_(U_A) f`. Uniqueness of sums
  gives the claim.

## 4. The main theorem

`unequalEulerFactorization_of_premises (hA hB hU) : UnequalEulerFactorizationStatement`.

Fix the data `F`, `ψ`, `r`, `t < r`, `T`, `T'`, `P`, `P'`, `S`. Choose:

* `C` from `UnequalUnfoldingStatement` for `T`, `T'`;
* `σ₁` from `exists_partialEulerFactor_convergence P P' hP hP'`;
* Satake bounds `A₀` for `P` and `B₀` for `P'`, and `σ₂` from
  `exists_hasSum_localTerm h A₀ B₀`.

Take `σ = max(C, σ₁, σ₂)`. This `σ` is chosen before the vectors, as the statement
requires. Let `x`, `x'` be spherical outside `S`, `W = W_x`, `W' = W'_x'`, and
`σ < Re s`.

1. Integrability of the integrand: the first part of `UnequalUnfoldingStatement` with
   `ψ.complex`, which is standard.
2. Summability and the product: `σ₁ < Re s` gives both, with
   `p = partialEulerProduct P P' hP hP' s`.
3. The identity. `partialUnequalWhittakerIntegral_eq_setIntegral` writes
   `Ψ_(S∪∞)` as `∫_(U_S) f`, and the full integral is `∫ f`. It remains to show
   `∫ f = p · ∫_(U_S) f`, which is `integral_eq_hasProd_mul_setIntegral`. Its step
   hypothesis is proved for each finite `A ⊇ S` and each `v ∉ A` as follows:
   * `FiniteAdditiveSupport ψ S` gives the component `ψ_v` with conductor `0`. So the
     standard character of `ψ_v` (rank `r + 1`) and the inverse standard character
     (rank `t + 1`) are integrally trivial.
   * `Unramified.Eigenvalues.ofTuple_surjective` gives tuples `a`, `b` enumerating the
     Satake parameters of `P`, `P'` at `v`. Then (A) applied to `T`, `P`, `x` (first
     conjunct) and to `T'`, `P'`, `x'` (second conjunct), with `ϖ = placeUniformizer v`,
     gives the factorizations of `W` and `W'` at `v`.
   * The kernel is left `N(𝔸)`-invariant (`ordinaryKernel_whittaker_unipotent_mul`).
   * The Satake bounds hold for every entry of `a` and `b`, and `q_v ≥ 2`, so
     `σ₂ < Re s` gives `HasSum (localTerm q_v a b s) (∏_(i,j)(1 - a_i b_j q_v^(-s)))⁻¹`.
   * By `pairEulerPolynomial_ofTuple`, this value is `partialEulerFactor P P' hP hP' v s`.
   * `setIntegral_insert_eq_mul` now gives the step.

`unequalEulerFactorizationReduction` is `fun hA hB hU => unequalEulerFactorization_of_premises
hA hB hU`. The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## 5. Provenance

Source: J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart
(eds.), *An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3). In §2.2, printed p.206,
Cogdell factors `Ψ(s; W_φ, W'_φ')` for factorizable cusp forms into local integrals and
evaluates the unramified ones by Theorem 3.3, printed p.215. The Library's target replaces
the product of local integrals over `S ∪ ∞` by the global partial integral `Ψ_(S∪∞)` over
`U_S` (see the target's Markdown). So the argument here is a global form of Cogdell's. Each
step from `A` to `A ∪ {v}` is the unramified computation of Theorem 3.3 carried out inside
the global integral: the cell decomposition (B_v) plays the role of the Iwasawa integration
formula on `N_m(F_v) \ GL_m(F_v)`, and the local Cauchy sum `exists_hasSum_localTerm` plays
the role of the Shintani–Casselman–Shalika evaluation of the local integral. The places are
added one at a time by `integral_eq_hasProd_mul_setIntegral`. The splitting into the three
premises and the helper lemmas is internal. The premises are the inputs the Library lacked
when the reduction was written (each now has a separate published proof):
the factorization of global Whittaker functions at unramified places (Cogdell p.206,
"`W_φ(g) = ∏_v W_(φ_v)(g_v)`" with the normalized spherical vector), the local integration
formula, and the absolute convergence of `Ψ(s; W, W')` (Cogdell p.206, gauge estimates).
