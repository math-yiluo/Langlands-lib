# A conditional proof of the unequal-rank semi-local functional equation

`Langlands.Global.RankinSelbergGlobal.UnequalSemilocalEquationReductionStatement.{u, uQ}`
is the Prop-valued statement

`UnequalSemilocalFactorizationStatement.{u, uQ} → UnequalSemilocalEquationStatement.{u, uQ}`.

The module proves it as `unequalSemilocalEquationReduction`, by the theorem
`unequalSemilocalEquation_of_factorization`. The premise
`UnequalSemilocalFactorizationStatement`, defined in the module of the same name, remains
open. It covers the factorization of the partial integrals into local integrals at `S`
and an archimedean factor, together with the archimedean functional equation and the
sign cancellation. This is therefore a conditional result. It does not prove
`UnequalSemilocalEquationStatement`. The proofs use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3): the proof of Theorem 4.1,
printed pp.219–220. The local functional equations at the places of `S` are Theorem 3.2
(p.214). In the reduction they come from the Library rather than from the premise.

## Library results used

* `canonicalFiniteAdditiveComponent ψ hdiag v`, with its specification
  `isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent`: a canonical
  component `ψ0_v` of `ψ` at each finite place.
* `Correspondence.localSelfDualHaar`, with `isSelfDual_localSelfDualHaar` and the
  uniqueness `eq_localSelfDualHaar`: the self-dual measure `ν0_v` for `ψ0_v`.
* `Automorphic.CuspidalPairPartialGamma.localGenericity`: the actual local components
  `π_v`, `π'_v` of `P`, `P'` are generic for `ψ0_v`.
* `RankinSelberg.genericPairGammaFactor_isPadic`: a unit `G0_v` of the rational functions
  with `IsPadicPairGammaFactor` for `(π_v, π'_v)`. Being a unit, it is nonzero.
* `RankinSelberg.isPadicSymmetricGammaFactor_of_le`: for `t ≤ r`, the symmetric relation
  of the target is the pair relation.
* `HasRationalContinuation.unique` and `GammaFunctionalEquation.gamma_unique`.
* `RankinSelberg.analyticAt_polynomial_spectralPoint`,
  `polynomial_spectralPoint_eventually_ne_zero`,
  `polynomial_reflected_spectralPoint_eventually_ne_zero` and
  `eventually_codiscrete_iff_forall_eventually_nhdsNE`. Together these say that
  `s ↦ p(q^(−s))` is entire, and that it is nonzero off a discrete set when `p ≠ 0`.

## Helper lemmas (namespace `UnequalSemilocalReduction`)

* `meromorphicOn_eval_spectralPoint`: for `q > 1`, `s ↦ R(q^(−s))` is meromorphic on `ℂ`,
  as the quotient of the analytic functions `num R (q^(−s))` and `denom R (q^(−s))`.
* `eventually_denom_ne_zero`, `eventually_denom_reflected_ne_zero`,
  `eventually_eval_ne_zero`: `denom R (q^(−s))` and `denom R (q^(−(1 − s)))` are nonzero
  off a discrete set. If `R ≠ 0`, so is `R(q^(−s))`.
* `rdual_ne_zero`: suppose `GammaFunctionalEquation q ζ e G R Rdual` holds with `G ≠ 0`
  and `R ≠ 0`. Then `Rdual ≠ 0`. If `Rdual = 0`, the equation also holds with `0` in
  place of `G`, and `gamma_unique` forces `G = 0`.
* `canonicalFiniteAdditiveComponent_unique`: two canonical components of `ψ` at `v` are
  equal, since `IsCanonicalFiniteAdditiveComponent` prescribes every value.
* `PadicUnequalTestData.exists_gammaEquation`: let `D` be p-adic test data for `(π, σ)`
  and `G` a rational function with `IsPadicPairGammaFactor K ψ ν π σ G`. Then there are
  `ζ` with `D.HasMinusOneScalar ζ` and rational functions `R`, `Rdual` such that:
  `R` continues `D.integral h ν`; `Rdual` continues `D.dualIntegral h ν`; and
  `GammaFunctionalEquation q ζ r G R Rdual` holds, where `q` is the residue cardinality.
  The proof unfolds `IsPadicPairGammaFactor` to `IsUnequalRankGammaFactor` (the case
  `t < r` of `IsPairGammaFactor`). It applies the fourth clause to the measure and
  functionals of `D`, and the resulting `UnequalRankGammaEquation` at block `j = 0`,
  `k = r − t − 1` to the vectors of `D`.

## Proof of `unequalSemilocalEquation_of_factorization`

Fix the data of the target. Apply the premise to `ψ0` and `ν0`. This gives `x`, `x'`
spherical outside `S`, a real `σ0`, functions `Ainf`, `Binf`, local data `D v` at `v ∈ S`,
and the clauses of the premise. Clause 2 supplies nonzero continuations `R_v` of
`(D v).integral`.

1. **Local gamma factors.** For `v ∈ S`, `localGenericity` and
   `genericPairGammaFactor_isPadic` give `G0_v ≠ 0` with `IsPadicPairGammaFactor`.
   `exists_gammaEquation` then gives `ζ0_v`, a continuation `R'_v` of `(D v).integral`, a
   continuation `Rd_v` of `(D v).dualIntegral`, and the gamma functional equation. By
   uniqueness of continuations (`q_v > 1`), `R'_v = R_v`. By `rdual_ne_zero`, `Rd_v ≠ 0`.
2. **The functions.** Let `a_v` and `ad_v` be the abscissas of the continuations `R_v`
   and `Rd_v`. Take `σ = max σ0 M` with `M ≥ max a_v ad_v` for all `v ∈ S`
   (`Finite.exists_le`), and set
   `A(s) = Ainf(s) ∏_(v ∈ S) R_v(q_v^(−s))` and `B(s) = Binf(s) ∏_(v ∈ S) Rd_v(q_v^(−s))`.
3. **Clauses 1–3 of the target.** Meromorphy follows from that of `Ainf`, `Binf` and
   `meromorphicOn_eval_spectralPoint`. For `σ < Re s`, clauses 3 and 4 of the premise
   rewrite the partial integrals, and the continuations identify each local integral
   with `R_v(q_v^(−s))`, respectively `Rd_v(q_v^(−s))`. Nonvanishing off a discrete set
   holds factorwise: for `Ainf`, `Binf` by the premise, and for the local factors by
   `eventually_eval_ne_zero` with `R_v ≠ 0`, `Rd_v ≠ 0`. A finite intersection of
   codiscrete sets is codiscrete (`Filter.eventually_all`).
4. **Clause 4 of the target.** Let `ψv`, `νv` and `G` be given. By
   `canonicalFiniteAdditiveComponent_unique` and `eq_localSelfDualHaar`, `ψv = ψ0` and
   `νv = ν0`; both are substituted. For `v ∈ S`, `isPadicSymmetricGammaFactor_of_le`
   turns the hypothesis on `G v` into `IsPadicPairGammaFactor`, and `exists_gammaEquation`
   gives `ζ_v` and a gamma functional equation for `G v`. Its continuations equal `R_v`
   and `Rd_v` by uniqueness. Off a discrete set, the denominators of `R_v(q_v^(−s))`,
   `Rd_v(q_v^(−(1 − s)))` and `G_v(q_v^(−s))` do not vanish, and clause 5 of the premise
   holds for this `ζ`. There each local equation reads
   `Rd_v(q_v^(−(1 − s))) = ζ_v^r G_v(q_v^(−s)) R_v(q_v^(−s))`. Their product over `S` is
   `∏ Rd_v(q_v^(−(1 − s))) = (∏ ζ_v^r)(∏ G_v(q_v^(−s)))(∏ R_v(q_v^(−s)))`. Substituting it
   into `L_∞(s) B(1 − s)`, the identity
   `L_∞(s) B(1 − s) = (∏_(v ∈ S) G_v(q_v^(−s))) ε_∞(s) L∨_∞(1 − s) A(s)` is clause 5 of the
   premise multiplied by `(∏ G_v(q_v^(−s)))(∏ R_v(q_v^(−s)))` (`linear_combination`). The
   product over `v ∈ S` of the target is rewritten as a product over the subtype `S`
   (`Finset.prod_coe_sort`).

The hypothesis `FiniteAdditiveSupport ψ S` and the contragredient data are used only
through the premise. The module declares the same two local instances as the target
(`GroupScheme.GeneralLinear.isAffine_groupScheme`, `GroupScheme.GeneralLinear.smoothStatement`).

## Provenance

Internal intermediate result towards `UnequalSemilocalEquationStatement`. The
argument is Cogdell's (pp.219–220). The finite-place input is the Library's
nonarchimedean gamma factor theory, so the retained premise concerns only the
factorization and the archimedean places.
