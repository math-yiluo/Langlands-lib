# Reduction of the cuspidal-pair continuation to the partial equation with integral gamma factors

Module `Langlands.Global.Factors.CuspidalPairPartialGammaReduction`. Author: Worker 5670.

## 1. Content and provenance

The module
[`CuspidalPairCompletedEquationReduction`](CuspidalPairCompletedEquationReduction.md) proves
`CuspidalSatakeBoundStatement.{u, uQ} → CuspidalPairContinuationStatement.{u, uQ} →
CuspidalPairCompletedEquationStatement.{u, uQ}`. The present module reduces the second premise
further. It contains:

* the statement `CuspidalPairPartialGammaEquationStatement` (called (G') below): a partial
  functional equation, over the places outside a finite set `S`, with the integral
  (Jacquet–Piatetski-Shapiro–Shalika) gamma factors of the actual local components at the
  finite places of `S`;
* the statement `CuspidalPairPartialGammaReductionStatement.{u, uQ}`, which is
  `CuspidalPairPartialGammaEquationStatement.{u, uQ} → CuspidalPairContinuationStatement.{u, uQ}`;
* the theorem `cuspidalPairPartialGammaReduction`, which proves
  `CuspidalPairPartialGammaReductionStatement`, with the lemmas it uses;
* the corollary `cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma`:
  `CuspidalSatakeBoundStatement.{u, uQ}` and `CuspidalPairPartialGammaEquationStatement.{u, uQ}`
  together imply the published `CuspidalPairCompletedEquationStatement.{u, uQ}`.

The theorem is a reduction: it does not prove the target, and (G') is an open premise
(Section 4). It is an intermediate result of Task 5721 in the sense of the "Intermediate
results" section of that task's revision 2. It discharges two parts of the continuation
statement from the Library: the comparison, at the finite places of `S`, of the
classification factors in `FinitePairFactorChoice` with the integral gamma factors of the
actual local components, and the passage from the partial L-functions to the completed ones.

**Source of (G').** Cogdell, *Analytic theory of L-functions for GL_n* (2004)
(`cogdell-2004-analytic-theory-gln`), proof of Theorem 4.1, printed pp.219–220 (PDF
pp.222–223). There `S` is a finite set of places, including the archimedean ones, outside which
everything is unramified. For `m < n` and suitable cusp forms `φ`, `φ'`, unfolding and the
unramified computation give, for `Re(s) ≫ 0`,
`I(s; φ, φ') = (∏_(v ∈ S) Ψ_v(s; W_v, W'_v)) L^S(s, π × π')`. The global functional equation is
`I(s; φ, φ') = Ĩ(1 - s; φ̃, φ̃')`. The local functional equation at each `v ∈ S` is
`Ψ_v(1 - s; ρ(w_(n,m)) W̃_v, W̃'_v)/L(1 - s, π̃_v × π̃'_v) =
ω'_v(-1)^(n-1) ε(s, π_v × π'_v, ψ_v) Ψ_v(s; W_v, W'_v)/L(s, π_v × π'_v)`. Cogdell divides by
the local L-factors at `v ∈ S`. Keeping them instead, the same three identities give the partial
equation

```text
L^S(s, π × π') = (∏_(v ∈ S) ω'_v(-1)^(n-1) γ_v(s)) L^S(1 - s, π̃ × π̃'),
γ_v(s) = ε(s, π_v × π'_v, ψ_v) L(1 - s, π̃_v × π̃'_v) / L(s, π_v × π'_v).
```

In the last step Cogdell notes that `ω'_v(-1) = 1` for `v ∉ S` and absorbs the signs into the
global ε-factor. In the convention used here they cancel: `∏_(v ∈ S) ω'_v(-1) = ω'(-1) = 1`,
since the central character `ω'` is trivial on `F^×` (this step is ours, not quoted). Multiplying by the archimedean L-factors moves the places at infinity
into `Λ^S = L_∞ L^S`, with `γ_∞(s) L_∞(s) = ε_∞(s) L_∞(1 - s, π̃_∞ × π̃'_∞)`. This gives (G').
The gamma factor convention is that of Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
convolutions* (1983) (`jpss-1983-rankin-selberg`), Theorem 2.7, printed pp.390–391, and (2.12),
printed p.403: the representation of larger rank is read first. The Library implements it as
`RankinSelberg.IsPadicSymmetricGammaFactor`, with
`γ = ε L(1 - s, π̃ × σ̃)/L(s, π × σ)`
([`PadicPairFactors`](../../Representation/RankinSelberg/PadicPairFactors.md)).

**Provenance (internal).** (G') is not a statement of the source. It is derived from the proof
above, in the conventions of the published target:

* The binders and hypotheses are those of `CuspidalPairCompletedEquationStatement`, in the same
  order and with the same `classical` elaboration and the same `let`-definitions of
  `infiniteL`, `dualInfiniteL` and `infiniteEpsilon`, except that (G') takes no factor choice
  `c : FinitePairFactorChoice …` and no `c.IsUnramifiedOutside S`. The hypotheses
  `HasIrreducibleAdmissibleComponents Pd` and `… Pd'` are kept (as `_hd`, `_hd'`), although
  the conclusion does not use them.
* Outside `S` the factors are the Euler factors of the Satake spectra of the presentations,
  `partialEulerFactor` from
  [`CuspidalPairBoundaryNonvanishingStatement`](CuspidalPairBoundaryNonvanishingStatement.md).
  At the finite places of `S` the factors are integral gamma factors of the actual local
  components, not the classification factors of a factor choice.
* As in `CuspidalPairContinuationStatement`, the identification of `Λ` with the Euler product
  is required only where the product converges, and convergence is not asserted. Unlike there,
  the conditions for `Λ` and `Λd` are separate (see Section 3).
* The signs `ω'_v(-1)^(n-1)` do not appear: the equation is stated after their cancellation.

## 2. Statements

Notation: `q_v = residueCardinality v`, `X_v(s) = RankinSelberg.spectralPoint q_v s = q_v^(-s)`.

`CuspidalPairPartialGammaEquationStatement.{u, uQ}`: for every number field `F : Type u` with
`CompactSpace (AdeleQuotient F)`, every unitary additive character `ψ` of the adeles that is
nontrivial and trivial on `F`, every `r t : ℕ`, cuspidal realizations `T Td` of rank `r + 1`
and `T' Td'` of rank `t + 1` with `Td` contragredient to `T` and `Td'` contragredient to `T'`,
presentations `P P' Pd Pd'` (universe `uQ`) with irreducible admissible components, every
finite set `S` of finite places containing the four exceptional sets with
`FiniteAdditiveSupport ψ S`, and every family of archimedean additive components `aR`, `aC` and
parameter lists `dR dR' dRd dRd'`, `dC dC' dCd dCd'` with their specifications, there are
`σ : ℝ` and `Λ Λd : ℂ → ℂ` such that

1. `MeromorphicOn Λ Set.univ` and `MeromorphicOn Λd Set.univ`;
2. for every `s` with `σ < s.re` and every `p : ℂ`, if
   `HasProd (fun v => partialEulerFactor P P' hP hP' v s) p` (a product over the finite places
   `v ∉ S`), then `Λ s = infiniteL s * p`;
3. for every `s` with `σ < s.re` and every `pd : ℂ`, if
   `HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) pd`, then
   `Λd s = dualInfiniteL s * pd`;
4. for every family `ψv` of finite additive characters with
   `IsCanonicalFiniteAdditiveComponent ψ v (ψv v)`, every family `νv` of local additive Haar
   measures that are self-dual for `ψv v`, and every `G : FinitePlace F →
   RankinSelberg.RationalFunctions` such that, for every `v ∈ S`, `G v` is an integral gamma
   factor of the actual local components,
   `RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v) ρ_v ρ'_v (G v)`
   with `ρ_v = ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation` and
   `ρ'_v` the same for `P'` (canonical topologies), one has, off a discrete subset of `ℂ`
   (`∀ᶠ s in Filter.codiscrete ℂ`),
   `Λ s = (∏_(v ∈ S) (G v)(X_v(s))) * infiniteEpsilon s * Λd (1 - s)`, where `(G v)(X_v(s))` is
   `RatFunc.eval (RingHom.id ℂ) (X_v(s)) (G v)`.

Here `partialEulerFactor P P' hP hP' v s` is
`((pairEulerPolynomial A_v A'_v).eval (X_v(s)))⁻¹`, with `A_v`, `A'_v` the Satake multisets
`P.spectralSystem.eigenvalues v _` and `P'.spectralSystem.eigenvalues v _`. In item 4 the
condition on `G v` is imposed only for `v ∈ S`, and only these values enter the product. By
`IsPadicSymmetricGammaFactor.unique` (proved in `PadicPairFactors`), the value `G v` for
`v ∈ S` is determined by `ψv v` and `νv v`; this lemma is not used in the proofs below.

`CuspidalPairPartialGammaReductionStatement.{u, uQ}`:
`CuspidalPairPartialGammaEquationStatement.{u, uQ} → CuspidalPairContinuationStatement.{u, uQ}`.

## 3. The proof

**Local genericity.** `Langlands.Automorphic.CuspidalPairPartialGamma.localGenericity` proves
the published `Langlands.Automorphic.CuspidalLocalGenericityStatement.{u, uQ}`. It repeats the
proof of the published `cuspidalUnitaryLocalGenericity`, which does not use the unitary
hypothesis: the local character `CuspidalWhittaker.localCharacter F v` is nontrivial
(`exists_localCharacter_ne_one`) and trivial on the integers (`localCharacter_eq_one`); the
local component has a nonzero Whittaker functional for it (`exists_localWhittakerFunctional`);
and `LocalRealization.isGeneric_of_integerTrivial_character` gives genericity for every
nontrivial unitary additive character. The name lies in a module-specific namespace so that it
does not collide with a later proof of that statement under its own task.

**Product lemmas** (namespace `Langlands.Global.CuspidalPairPartialGamma`):

* `hasProd_subtype_notMem`: if `HasProd f p` for `f : ι → ℂ` and `f i ≠ 0` for `i ∈ S`, then the
  product of `f` over `{i // i ∉ S}` has value `p * ∏_(i ∈ S) (f i)⁻¹`. Multiply by the function
  equal to `(f i)⁻¹` on `S` and to `1` elsewhere (`hasProd_prod_of_ne_finset_one`,
  `HasProd.mul`), and restrict along `Subtype.val` (`Function.Injective.hasProd_iff`).
* `prod_mul_eq_of_hasProd`: if `HasProd f p`, `g` is `f` restricted to the complement of `S`,
  and `Λ = L * p'` whenever `HasProd g p'`, then `(∏_(i ∈ S) f i) * Λ = L * p`. If no `f i`
  with `i ∈ S` vanishes, apply the previous lemma. Otherwise both sides vanish: the left factor
  is `0`, and `p = 0` by `hasProd_zero_of_exists_eq_zero` and `HasProd.unique`.

The second case is why (G') has separate convergence conditions for `Λ` and `Λd`. In Lean
`c.finiteL v s = ((c.lPolynomial v).eval (X_v(s)))⁻¹` is `0` where the polynomial vanishes, and
then the complete Euler product has value `0` while the partial product need not converge.
A joint condition on both partial products would then give no information about `Λ` from the
convergence of the complete product of `L`.

**Factor-choice lemmas** (namespace
`Langlands.Global.CuspidalPairFunctionalEquation.FinitePairFactorChoice`, for a factor choice
`c`):

* `one_lt_residueCardinality`, `meromorphicOn_finiteL`, `meromorphicOn_finiteDualL`:
  `s ↦ c.finiteL v s` and `s ↦ c.finiteDualL v s` are meromorphic on `ℂ`, as inverses of the
  analytic functions `s ↦ P(q_v^(-s))` (`RankinSelberg.analyticAt_polynomial_spectralPoint`).
* `isSmoothDual_localClass`: if `Td` is contragredient to `T`, then the local class of `Pd`
  at `v` is the smooth dual of that of `P`. This is the published
  `Automorphic.cuspidalContragredientLocalCompatibility`, which gives an equivalence of the
  actual local component of `Pd` with the smooth contragredient of that of `P`.
* `isPadicSymmetricGammaFactor`: the rational gamma expression
  `rationalGammaExpression δ_v c_v m_v P_v P∨_v` built from the classification factors of `c`
  (`δ_v = residueReflection`, `(c_v, m_v) = c.epsilon v`, `P_v = c.lPolynomial v`,
  `P∨_v = c.dualLPolynomial v`) is an integral gamma factor of the actual local components:
  `IsPadicSymmetricGammaFactor (padicField v) (c.additive v) (c.measure v) ρ_v ρ'_v _`. The
  published `Correspondence.hasGenericAutomorphicGammaComparison`, applied to the proved
  `RankinSelberg.genericLanglandsPairEpsilonFactorComparison`, turns a class-level gamma
  certificate into this relation for generic components. Genericity is `localGenericity`. The
  class-level certificate consists of the two smooth duals from `isSmoothDual_localClass` and
  the specifications `c.lPolynomial_spec`, `c.dualLPolynomial_spec`, `c.epsilon_spec`.
* `eventually_finiteL_mul_gamma`: off a discrete set,
  `c.finiteL v s * γ_v(s) = c.finiteEpsilon v s * c.finiteDualL v (1 - s)`, with `γ_v(s)` the
  evaluation of that expression at `X_v(s)`. Both polynomials are nonzero, so near every point,
  except possibly at the point itself, `P_v(X_v(s)) ≠ 0` and `P∨_v(X_v(1 - s)) ≠ 0`
  (`polynomial_spectralPoint_eventually_ne_zero`,
  `polynomial_reflected_spectralPoint_eventually_ne_zero`,
  `eventually_codiscrete_iff_forall_eventually_nhdsNE`). There `eval_rationalGammaExpression`
  evaluates `γ_v(s)` as `c_v X_v(s)^(m_v) P_v(X_v(s)) / P∨_v(δ_v/X_v(s))`, and
  `δ_v / X_v(s) = X_v(1 - s)` (`coe_residueReflection`, `spectralPoint_one_sub`); `field_simp`
  concludes.
* `continuationHolds_of_partialGamma`: given `σ`, `Λ`, `Λd` with items 1–3 of (G'), an
  `S`-indexed family `G` of functions with
  `Λ s = (∏_(v ∈ S) G v s) * εinf s * Λd (1 - s)` off a discrete set, and
  `c.finiteL v s * G v s = c.finiteEpsilon v s * c.finiteDualL v (1 - s)` off a discrete set for
  each `v ∈ S`, if `c.IsUnramifiedOutside S` then `c.ContinuationHolds S Linf Ldinf εinf`. The
  witnesses are `σ`, `s ↦ (∏_(v ∈ S) c.finiteL v s) * Λ s` and
  `s ↦ (∏_(v ∈ S) c.finiteDualL v s) * Λd s`. They are meromorphic (`MeromorphicOn.fun_prod`,
  `MeromorphicOn.mul`). Outside `S`, `IsUnramifiedOutside` identifies `c.finiteL v s` with
  `partialEulerFactor P P' hP hP' v s`, and `c.finiteDualL v s` with the dual one, so
  `prod_mul_eq_of_hasProd` gives the two product identities. For the functional equation, the
  finitely many local identities hold simultaneously off a discrete set
  (`Filter.eventually_all_finset`); multiplying the equation for `Λ` by
  `∏_(v ∈ S) c.finiteL v s` and substituting them gives
  `(∏_(v ∈ S) c.finiteEpsilon v s) * εinf s * ((∏_(v ∈ S) c.finiteDualL v (1 - s)) * Λd (1 - s))`.

**The reduction.** `cuspidalPairPartialGammaReduction` introduces the binders of
`CuspidalPairContinuationStatement`, applies (G') to the same data (without `c`), and applies
`continuationHolds_of_partialGamma` with `G v` the gamma expression of `c` at `v`. Item 4 of (G')
is used with `ψv = c.additive`, `νv = c.measure` and these `G v`, whose hypothesis is
`isPadicSymmetricGammaFactor`; the local identities are `eventually_finiteL_mul_gamma`. The
`let`-definitions of the archimedean products are elaborated identically in both statements.

`cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma` composes this with
`cuspidalPairCompletedEquationReduction`. The Lean service reports that it depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## 4. Scope and remaining work

* (G') is open. Of the obligations in section 8 of
  [`CuspidalPairFunctionalEquationStatement.md`](CuspidalPairFunctionalEquationStatement.md),
  it retains item 1 (the global Rankin–Selberg theory), item 3 (the archimedean parameters,
  the independence of the factors from the parameter lists, and the archimedean local theory),
  item 4 (the unramified computation and the identification of the Satake parameters), item 5
  (the norm shift) and item 6 (the sign cancellation). It also needs the local functional
  equations at the finite places of `S`, in the form of `IsPadicSymmetricGammaFactor`. The
  comparison part of item 2, at the places of `S`, is proved here, and so is the passage
  between partial and completed L-functions. Item 7 (absolute convergence) is the subject of
  `CuspidalSatakeBoundStatement` in `CuspidalPairCompletedEquationReduction`.
* The premise `CuspidalSatakeBoundStatement` of the corollary is the one of
  `CuspidalPairCompletedEquationReduction` and is not treated here.
* Item 4 of (G') quantifies over every integral gamma factor `G v`, `v ∈ S`; it does not assert
  that one exists. The reduction supplies one from the factor choice `c`.
* The module proves `CuspidalLocalGenericityStatement` as an auxiliary result, under a
  module-specific name. It makes no other claim about that statement.
