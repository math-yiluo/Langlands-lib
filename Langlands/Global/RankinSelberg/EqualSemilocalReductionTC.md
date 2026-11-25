# Totally complex form of the equal-rank semi-local reduction

Module `Langlands.Global.RankinSelberg.EqualSemilocalReductionTC`.

## 1. Content and status

This module contains, in the namespace `Langlands.Global.RankinSelbergGlobal`:

* the Prop-valued premise `EqualSemilocalFactorizationTCStatement.{u, uQ}`, the totally
  complex form of the published premise `EqualSemilocalFactorizationStatement.{u, uQ}`
  (module [`EqualSemilocalReduction`](EqualSemilocalReduction.md), Section 3 there);
* the statement `EqualSemilocalReductionTCStatement.{u, uQ}`, the implication
  `EqualSemilocalFactorizationTCStatement.{u, uQ} → EqualSemilocalEquationTCStatement.{u, uQ}`;
  the conclusion is the totally complex form of `EqualSemilocalEquationStatement`, published
  in the module [`SemilocalEquationTCStatements`](SemilocalEquationTCStatements.md);
* the theorem `equalSemilocalReductionTC : EqualSemilocalReductionTCStatement.{u, uQ}`, which
  proves this implication (Section 4);
* the theorem `equalSemilocalFactorizationTCStatement_of_general`: the general premise
  `EqualSemilocalFactorizationStatement.{u, uQ}` implies its totally complex form
  (Section 3).

The theorem is a **conditional reduction**. Its premise is an open statement, proved nowhere
in the Library, and the theorem does not prove `EqualSemilocalEquationTCStatement`. It is an
intermediate result towards `EqualSemilocalEquationStatement`, whose unconditional proof
stays open.

## 2. Provenance

The content is **derived**. Both propositions in this module are the published propositions
with one more instance argument. The proof is the published proof of
`equalSemilocalReduction` with one more binder in its `intro`.

The restriction to totally complex base fields follows the Library's route to the local
correspondence, which uses the
global Rankin–Selberg results only over the CM field produced by the globalization of
Henniart (2000, §3) and Harris (1998, §4), and over its finite extensions. All these fields
are totally complex (`NumberField.IsCMField.isTotallyComplex`,
`NumberField.isTotallyComplex_of_algebra`).

The mathematical sources are those of the published module, unchanged: J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), registered as
`cogdell-2004-analytic-theory-gln`, proof of Theorem 4.1, printed pp.219–220, with Theorem 3.2,
p.214, and the archimedean theory of §3.2, pp.216–217. The correspondence between each clause
of the premise and the source is given in Section 3 of
[`EqualSemilocalReduction.md`](EqualSemilocalReduction.md).

## 3. The premise `EqualSemilocalFactorizationTCStatement`

The proposition is `EqualSemilocalFactorizationStatement` with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`. The universe levels `u`
(number field) and `uQ` (spectral presentations) are the same, and the rest of the body is
verbatim. The original implies it by forgetting the instance: this is the theorem
`equalSemilocalFactorizationTCStatement_of_general`, proved by `fun F _ _ _ _ => h F`.

Over a totally complex field there is no real place, so the index type
`{v : InfinitePlace F // v.IsReal}` is empty. The real-place products in `infiniteL`,
`dualInfiniteL` and `infiniteEpsilon` are then empty products, equal to `1`, and the
real-place hypotheses (`aR`, `dR`, `dR'`, `dRd`, `dRd'`) are vacuous. Only the complex-place
(`GL_n(ℂ)`) archimedean factors remain. Lean does not simplify these products in the
statement; they are kept verbatim so that the two forms correspond literally.

In prose: for a totally complex number field `F`, in the setting of
`EqualSemilocalEquationTCStatement` and for canonical finite components `ψv` of `ψ` with
self-dual measures `νv`, there are vectors `x`, `x'` spherical outside `S`, a Schwartz–Bruhat
`Φ` standard outside `S`, a real `σ`, meromorphic functions `Z`, `Zd` on `ℂ` that vanish only on
a discrete set, a constant `κ` and local test data `D v` (`EqualLocalTestData`) for the actual
local components at the places `v ∈ S`, such that:

1. the local integrals of each `D v` and their duals are not identically zero on any right
   half-plane;
2. `κ ∏_(v ∈ S) ζ_v^r = 1` whenever each `ζ_v` is the scalar of `−1` on the model of the second
   local component;
3. off a discrete set, `L_∞(s) Zd(1 − s) = κ ε_∞(s) L∨_∞(1 − s) Z(s)`;
4. on `σ < Re s`, `Ψ_(S∪∞)(s; W, W', Φ) = Z(s) ∏_(v ∈ S) Ψ_v(s; D v)` and
   `Ψ_(S∪∞)(s; W̃, W̃', Φ̂) = Zd(s) ∏_(v ∈ S) Ψ_v(s; D̃ v)`.

## 4. The proof of `equalSemilocalReductionTC`

The published proof of `equalSemilocalReduction` introduces the premise `hfac` and then the
binders of the conclusion, starting with the field `F` and its instances. It applies `hfac`
only once, at the same `F` and the same data, together with the canonical families `ψ0`
(`canonicalFiniteAdditiveComponent`) and `ν0` (`localSelfDualHaar`). The proof here is the
same text. The only change is one more anonymous binder in the `intro`, for the instance
`[NumberField.IsTotallyComplex F]`. In the call `hfac F ψ …` that instance is found by
instance resolution.

The rest is unchanged; Section 5 of [`EqualSemilocalReduction.md`](EqualSemilocalReduction.md)
describes it:

* the rational continuations of the local integrals of `D v`, from
  `EqualLocalTestData.exists_continuations` (JPSS rationality, through `equalRankAnalytic`);
* `A = Z · ∏_(v ∈ S) R_v(q_v^(−s))` and `B = Zd · ∏_(v ∈ S) R̃_v(q_v^(−s))`, meromorphic and
  nonzero off a discrete set, equal to the partial integrals on a right half-plane;
* for every family of gamma factors `G`, the local functional equation at each `v ∈ S`
  (`EqualLocalTestData.exists_gammaEquation`, with the minus-one scalar `ζ_v`); then the
  archimedean equation and the sign identity `κ ∏ ζ_v^r = 1` close the identity by
  `linear_combination`. The given `ψv`, `νv` agree with `ψ0`, `ν0` by uniqueness of the
  canonical component and of the self-dual measure.

The two private helper lemmas of the published module, `canonicalComponent_unique` and
`one_lt_residueCardinality`, cannot be used from another module. They are copied here as the
private lemmas `canonicalComponent_unique_tc` and `one_lt_residueCardinality_tc`, with the same
statements and proofs. The two local instances for the general linear group scheme (affine
and smooth), which the statements need, are declared again under new names.

`equalSemilocalReductionTC` and `equalSemilocalFactorizationTCStatement_of_general` use only
the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## 5. The retained premise

The single open premise is `EqualSemilocalFactorizationTCStatement.{u, uQ}`. A proof of it,
or of the general `EqualSemilocalFactorizationStatement.{u, uQ}` (which implies it), gives
`EqualSemilocalEquationTCStatement.{u, uQ}` through `equalSemilocalReductionTC` (for the
general premise, after `equalSemilocalFactorizationTCStatement_of_general`). The general
premise is reduced by `equalSemilocalFactorizationReduction` (module
`EqualSemilocalFactorizationReduction`) to its missing inputs (the archimedean local theory,
the factorization over `S ∪ ∞` and the central sign), which are stated in
`ArchimedeanSemilocalTheoryStatement` and its statement modules; the central sign is proved
(`archimedeanCentralSign`, module `ArchimedeanCentralSignProof`). Over a totally
complex field only the complex places need the archimedean theory.
