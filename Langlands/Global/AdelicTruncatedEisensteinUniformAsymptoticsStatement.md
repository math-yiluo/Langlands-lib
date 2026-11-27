# Truncated Eisenstein families: asymptotics and locally uniform square integrability

Module `Langlands.Global.AdelicTruncatedEisensteinUniformAsymptoticsStatement`
states one proposition,
`Langlands.Global.LocalTruncatedEisensteinFamilyUniformInnerProductStatement`,
and proves that it implies
`Langlands.Global.LocalTruncatedEisensteinFamilyInnerProductStatement`
(`localTruncatedEisensteinFamilyInnerProduct_of_uniform`). The proposition
itself is not proved here.

## Sources

- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, in: On Certain L-Functions, Clay Math. Proc. 13 (2011),
  pp. 309–331, registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (volume PDF; PDF
  page = printed page + 9).
  - §2, p.312, Working hypothesis: for `φ ∈ A^2_P` and `λ_0` there are a
    neighbourhood `N` of `λ_0` and integers `n`, `m` such that
    `[∏_α ⟨λ − λ_0, α^∨⟩]^m E(·, φ, λ)` is a holomorphic function on `N` with
    values in the Fréchet space of smooth functions on `G(F) \ G(𝔸)` with the
    seminorms `sup_{g ∈ 𝔖} |R(X)f(g)| ‖g‖^{-n}`, `X ∈ U(𝔤_ℂ)`.
  - §3, p.313: Proposition 1 and formula (2), with the implied constant
    uniform for `(λ, λ')` in a compact set.
  - §4, Lemma 3, p.317 (PDF p.326): uniform exponential decay on a cone for
    a family of polynomial exponentials with at most `l` exponents in a fixed
    compact set negative with respect to the cone, bounded on a fixed
    neighbourhood.
  - §6, Corollary 2, p.323 (PDF p.332): bounded number of exponents of the
    constant terms, contained in a ball of radius `‖λ‖ + k`, with a finite set
    of real parts.
  - §7, (14), p.324, and the end of §7, p.325 (PDF pp.333–334): the remainder
    `R(T)` lies in `PE_{≤ l}(A + B_{‖λ‖+‖λ'‖+l}(i𝔞_0^*))`, and the uniformity
    of the error term follows from Lemma 3 applied to the family `R(λ, λ', T)`
    with `(λ, λ')` in a compact set.
  - §8, p.328: the proof of Proposition 2, which writes the truncated inner
    product of two wave packets as an integral over `μ ∈ i𝔞_G^*`, `λ`, `λ'`
    of `(Λ^T E_P(·, φ(λ + μ), λ), Λ^T E_{P'}(·, φ'(λ' + μ), λ'))` and replaces
    it, "by Proposition 1", by the integral (18) of the main terms.
- J. Arthur, *A trace formula for reductive groups II: applications of a
  truncation operator*, Compositio Math. 40 (1980), 87–121, registered as
  `arthur-1980-trace-formula-reductive-groups-II` (PDF page = printed page −
  85): §1, Lemma 1.4, pp.95–96, restated as Arthur 2005, Proposition 13.2 (b).
- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §4, p.24 (a
  suitable maximal compact `K`, citing Arthur 1981, p.9); §13, Proposition
  13.2, p.71 (PDF p.83). Part (b): given a Siegel set `𝔖`, positive integers
  `N`, `N₀` and an open compact subgroup `K₀` of `G(𝔸_fin)`, one can choose
  finitely many left invariant differential operators `X_i` on `G(ℝ)¹` and an
  integer `r` such that, for every measure space `(Ω, dω)` and every
  measurable map `ω ↦ φ(ω, ·)` from `Ω` to `C^r(G(F) \ G(𝔸)¹ / K₀)`,

  `sup_{x ∈ 𝔖} ‖x‖^N ∫_Ω |Λ^T φ(ω, x)| dω`  (13.5)

  is bounded by

  `sup_{y ∈ G(𝔸)¹} ‖y‖^{-N₀} ∑_i ∫_Ω |X_i φ(ω, y)| dω`  (13.6).

  The operators `X_i` and `r` are chosen before the measure space and the
  family. Arthur states that this is Lemma 1.4 of Arthur 1980.
- J. Arthur, *The trace formula in invariant form*, Ann. of Math. 114 (1981),
  1–74, registered as `arthur-1981-trace-formula-invariant-form`: §1, p.9,
  maximal compact subgroups admissible relative to `M_0`.

## The proposition

It is `LocalTruncatedEisensteinFamilyInnerProductStatement` (module
`Langlands.Global.AdelicTruncatedEisensteinFamilyAsymptoticsStatement`), whose
Markdown explains the setting, the normalizations, the family form of the
inducing data and the choice of one compact subgroup `K` with Arthur's
projection property and Proposition 1. The conjunct after `∀ D hρ hK₀ hK` is
now a conjunction of three parts instead of two: the projection property,
unchanged; the asymptotic formula, with a weaker hypothesis on the compact set
of parameters; and a third part, for the same `K`, `D`, `hρ` and `hK₀`.

**Second part: uniformity in the central parameter.** The data, the main term
and the conclusion are those of
`LocalTruncatedEisensteinFamilyInnerProductStatement`. The only change is the
hypothesis on the compact set `C` of coordinate pairs `(x, x')`: instead of
`restrictToTorus (e J x) ∈ relativeRootSpanReal i` and
`restrictToTorus (e J' x') ∈ relativeRootSpanReal i` (both parameters in
`(𝔞^G)^*`), it requires only

`restrictToTorus (e J x) − restrictToTorus (e J' x') ∈ relativeRootSpanReal i`,

that is, `λ = i e(x) ∈ i𝔞_P^*` and `λ' = i e'(x') ∈ i𝔞_{P'}^*` have the same
component `μ ∈ i𝔞_G^*`. The domain conditions `λ ∈ DE ∩ DM`,
`λ' ∈ DE' ∩ DM'` are unchanged.

Write `λ = λ_1 + μ`, `λ' = λ'_1 + μ` with `λ_1 ∈ i(𝔞_P^G)^*`,
`λ'_1 ∈ i(𝔞_{P'}^G)^*`. On `G(𝔸)¹`, where `H_G = 0`, the restriction of
`E(λ) = ∑_l b_l(λ) E_P(v_l, λ)` is the restriction of
`∑_l b_l(λ_1 + μ) E_P(v_l, λ_1)`, the series at `λ_1` of the shifted family
`φ(· + μ)`. The normalized intertwining operators `M(w, ·)` on `A^2_P` do not
change under a shift by `μ ∈ 𝔞_G^*`, so the coefficient functions evaluated at
`λ` are those of the expansions of `M(w, λ_1) φ(λ_1 + μ)`. In the main term,
`w` and `w'` fix the central component and the conjugation of the second
parameter sends `μ` to `−μ`, so the exponent `wλ + w'\bar λ'` and the
denominators involve only `λ_1`, `λ'_1`. Hence, for each fixed `μ`, the second
part is Lapid's (2) for the families `φ(· + μ)`, `φ'(· + μ)`; the new content
is that the error term is uniform also in `μ` in a compact set. Lapid's §8
uses exactly this uniformity when it replaces the integral over `μ`, `λ`, `λ'`
of truncated inner products by the integral (18) of the main terms. In Lapid's
proof of Proposition 1 the uniformity comes from Lemma 3 (p.317) applied to
the family `R(λ, λ', T) = J(T) − M(T)` with `(λ, λ')` in a compact set (end of
§7, p.325). Lemma 3 needs two inputs: a compact set of exponents, negative
with respect to the cone, containing the exponents of every member of the
family, with a common bound on their number; and a bound for the family that
is uniform on a fixed neighbourhood in the truncation variable. Both hold for
the family `R(λ_1, λ'_1, μ, T)` with `(λ_1, λ'_1, μ)` in a compact set:

- *Exponents.* The exponents of the constant terms are not fixed: they move
  with the parameter (already for split `SL₂` and its Borel subgroup, the
  identity summand of the constant term has exponent `λ_1`). What is fixed is
  the following. The shifted families take values in the finite-dimensional
  space spanned by the `v_l`, and the exponents of a combination lie among
  those of the `v_l`. So Corollary 2 (p.323), applied to the finitely many
  `v_l`, `v'_l`, gives one bound for the number of exponents, one finite set
  of real parts, and exponents in a ball of radius `‖λ_1‖ + k` (resp.
  `‖λ'_1‖ + k`). Then (14) (p.324) and the argument following it place `R` in
  `PE_{≤ l}(A + B_ρ(i𝔞_0^*))` with `l` and the finite set `0 ∉ A ⊆ 𝔞_{0,−}^*`
  independent of the parameters and with `ρ` bounded on the compact set of
  `(λ_1, λ'_1)`; this is one compact set of exponents, negative with respect
  to the cone, for the whole family.
- *Local bound.* For `T` in a compact neighbourhood `U` of a point of the
  cone, `J` is bounded uniformly in the parameters by the locally uniform
  bounds on truncated Eisenstein series (the argument of the third part), and
  `M` is continuous in `(λ_1, λ'_1, μ, T)` (it is smooth in the parameters by
  §7, p.325, before Lemma 7). So `R` is bounded on the compact set of triples
  times `U`.

Lemma 3 then gives `|R(λ_1, λ'_1, μ, T)| ≤ B e^{−δ‖T‖}` on the cone, uniformly
for `(λ_1, λ'_1, μ)` in the compact set.

If both parameters lie in `(𝔞^G)^*`, their difference lies in the root span,
so the published hypothesis implies the new one; this gives the implication
below.

**Third part.** For every closed matrix realization `rho` (with `hsmooth`,
`hcalc`), every Haar measure `μ₁` on `G(𝔸)¹` with quotient measure `μ_Q` on
`G(F) \ G(𝔸)¹`, every standard index `J`, every holomorphic family as in the
asymptotic formula (`v : Fin q → …` with every `v l ∈ A^2_P`,
`b : Fin q → X^*(P) ⊗ ℂ → ℂ` entire, `E` meromorphic in coordinates with
domain of holomorphy `DE` and equal to `∑_l b l λ · E_P(v l, λ)` for
`IsStandardRegularParameter D J.roots R λ`), every linear coordinates
`e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and every compact `C ⊆ ℝⁿ` with `i e(x) ∈ DE` for all
`x ∈ C`, there is `c₀` such that for every `T` with `β(T) > c₀` for all simple
roots `β`:

- the function `(x, y) ↦ Λ^T E(i e(x))(y)` on `ℝⁿ × G(F) \ G(𝔸)¹` is almost
  everywhere strongly measurable for `(volume.restrict C).prod μ_Q`;
- there is `B` with `Λ^T E(i e(x)) ∈ L²(μ_Q)` and
  `∫ |Λ^T E(i e(x))|² dμ_Q ≤ B` for every `x ∈ C`.

Here `Λ^T E(λ)` is `normOneTruncation hG hi D hK₀ hρ T` applied to the
restriction of `E(λ)` to `G(𝔸)¹`, evaluated at `y.out`. The parameters
`i e(x)` range over a compact subset of `i𝔞_P^*`, not of `i(𝔞_P^G)^*`. Only
the restriction of `E(λ)` to `G(𝔸)¹` enters. For `v l ∈ A^2_P` and
sufficiently regular `λ`, the restriction of each series `E_P(v l, λ)` to
`G(𝔸)¹` depends on `λ` only through its projection to `(𝔞_P^G)^*`, because
`H_P(γg)` has `𝔞_G`-component `H_G(g) = 0` there.

**Why the sources give the third part.** Fix `T` sufficiently regular and
the compact set `C`.

- *Common finite level.* Each of the finitely many inducing vectors `v_l` is
  right invariant under an open compact subgroup of `G(𝔸_fin)`. Intersecting
  these subgroups with the finite part of `K` gives one open compact `K₀`
  under which every `E_P(v_l, λ)` is right invariant for `λ` in the region of
  convergence. By scalar uniqueness of the continuation (for each `g`, both
  sides are holomorphic in `λ` on `DE` and agree on the regular region), every
  `E(λ)`, `λ ∈ DE`, is right invariant under `K₀`.
- *Uniform weighted derivative bounds.* By Lapid's Working hypothesis, near
  each point `λ_0` the product of `E_P(·, v_l, λ)` with a power of root
  functionals is holomorphic with values in the Fréchet space of smooth
  functions with the seminorms `sup_g |R(X)f(g)| ‖g‖^{-n}`. The family
  `E(λ) = ∑_l b_l(λ) E_P(v_l, λ)` is holomorphic in `λ` on `DE` for every `g`,
  so cancelling the root factors (division by a linear form of a holomorphic
  function vanishing on its zero set, pointwise in `g`) shows that `E` is
  holomorphic near each point of `DE` with values in that Fréchet space.
  Covering the compact set `{i e(x) : x ∈ C}` by finitely many such
  neighbourhoods bounds every seminorm `sup_g |R(X)E(i e(x))(g)| ‖g‖^{-n}`
  uniformly in `x ∈ C`.
- *Pointwise rapid decay.* Choose `X_i` and `r` by Arthur's estimate for a
  Siegel set `𝔖`, exponents `N`, `N₀` and the level `K₀`. For each `x ∈ C`,
  apply the estimate to the one-point measure space (the Dirac measure at
  `x`) and the family `E(i e(x))`. Since the operators and the bound do not
  depend on the measure space or the family, this gives
  `|Λ^T E(i e(x))(y)| ≤ B₁ ‖y‖^{-N}` for `y ∈ 𝔖` with one constant `B₁` for all
  `x ∈ C`. (Arthur's proof on p.96 compares norms of rational translates of
  points of `𝔖`, which turns bounds on Siegel representatives into the
  group-wide supremum in (13.6).)
- *The `L²` bound.* `G(F) \ G(𝔸)¹` is covered by the image of `𝔖`, on which
  `‖y‖^{-2N}` is integrable for large `N`. Integrating the square of the
  pointwise bound gives `∫ |Λ^T E(i e(x))|² dμ_Q ≤ B` for every `x ∈ C`.
- *Joint measurability.* `(x, g) ↦ E(i e(x))(g)` is measurable, the constant
  terms in `Λ^T` are integrals over compact quotients of unipotent groups, the
  chamber cutoffs are Borel, and the sums over rational cosets are pointwise
  finite; the result is invariant under `G(F)` and descends to the quotient.

These are properties of the suitable (admissible) `K` for which Arthur proves
Proposition 13.2, the `K` of the first two parts, for which the Markdown of
`LocalTruncatedEisensteinFamilyInnerProductStatement` gives the justification.
The proposition claims nothing for other compact subgroups.

**Use.** In Lapid's §8 the truncated inner product of two wave packets is
written, after Fourier transform in the central variable, as an integral over
`μ`, `λ`, `λ'` of truncated inner products of Eisenstein series, to which the
second part applies. The interchange of the integrals and the square
integrability of the truncated wave packets need the measurability and the
bound of the third part. The first two conclusions of the second part already
give square integrability of each slice for the admitted pairs of parameters,
but the error estimate there is conditional on nonvanishing denominators, so
it can be unavailable on the diagonal `λ = λ'`, where denominators of proper
standard parabolic subgroups may vanish. The third part supplies joint
measurability, a bound uniform over `C`, and the larger scope of all of
`i𝔞_P^*`.

## The implication

`localTruncatedEisensteinFamilyInnerProduct_of_uniform` takes the compact
subgroup of the proposition, keeps the projection property, obtains the
published asymptotic formula from the second part (the difference of two
elements of the submodule `relativeRootSpanReal i` lies in it,
`Submodule.sub_mem`), and drops the third part.
