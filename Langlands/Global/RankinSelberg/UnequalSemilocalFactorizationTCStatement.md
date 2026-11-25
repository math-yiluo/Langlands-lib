# Factorization premise of the unequal-rank semi-local equation over totally complex fields

`Langlands.Global.RankinSelbergGlobal.UnequalSemilocalFactorizationTCStatement.{u, uQ}`
is a Prop-valued statement. It is the totally complex form of the published premise
`UnequalSemilocalFactorizationStatement.{u, uQ}` (module
`Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationStatement`). Its first binders
are

`∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]`.

So `[NumberField.IsTotallyComplex F]` is inserted after `[NumberField F]`, at the same
universes `u` (number field) and `uQ` (spectral presentations). Everything after the binder
`[CompactSpace (AdeleQuotient F)]` is copied verbatim from the published premise, including
the local test data `PadicUnequalTestData` and its `integral`, `dualIntegral` and
`HasMinusOneScalar`, which are imported from that module. Nothing here proves the
statement. It is the open premise of the conditional proof of
`UnequalSemilocalEquationTCStatement` in the module
`Langlands.Global.RankinSelberg.UnequalSemilocalEquationTCReduction`.

## Content

The data are the same as in `UnequalSemilocalFactorizationStatement`, with `F` totally
complex:

* `ψ`, a unitary character of `𝔸_F`, trivial on `F`;
* `T`, `T'`, actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)`, with `t < r` and
  contragredients `Td`, `Td'`;
* spectral presentations `P`, `P'` with irreducible admissible components;
* `S`, a finite set of finite places containing both exceptional sets, outside which
  `ψ_v` has conductor `𝒪_v`;
* the archimedean additive components `aR`, `aC` and the archimedean parameters;
* canonical finite components `ψv` of `ψ` and measures `νv` self-dual for them.

Under these hypotheses, the statement asserts that there are:

* `x`, `x'` fixed by `GL(𝒪_v)` at every finite `v ∉ S`;
* a real `σ`;
* functions `Ainf`, `Binf` that are meromorphic on `ℂ` and nonzero off a discrete set;
* local test data `D v` at each `v ∈ S`, for the actual local components;

such that the following hold:

* each block-zero local integral `(D v).integral` has a nonzero rational continuation;
* for `σ < Re s`, `Ψ_(S∪∞)(s; W, W') = Ainf(s) ∏_(v ∈ S) Ψ(s; W_v, W'_v)`;
* for `σ < Re s`,
  `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃') = Binf(s) ∏_(v ∈ S) Ψ(s; ρ(w_(n,m)) W̃_v, W̃'_v)`;
* for every family `ζ` with `(D v).HasMinusOneScalar (ζ v)`, off a discrete set,
  `(∏_(v ∈ S) ζ_v^r) L_∞(s) Binf(1 − s) = ε_∞(s) L∨_∞(1 − s) Ainf(s)`.

The published premise's Markdown explains each object, the normalizations and the
comparison with Cogdell. All of that applies here unchanged.

**Effect of the totally complex hypothesis.** The statement still has the binders `aR`,
`dR`, `dR'`, `dRd`, `dRd'` and their hypotheses. A totally complex `F` has no real places,
so these are functions on an empty type, and the hypotheses on them are vacuous. The
real-place products in `infiniteL`, `dualInfiniteL` and `infiniteEpsilon` are empty
products, equal to `1`. What remains of the archimedean content is the complex places:
`complexPairLFactor` and `complexPairEpsilon`, normalized by `aC`, that is, the `GL_n(ℂ)`
theory of Jacquet and Shalika. The Lean statement does not perform this simplification;
it is the verbatim body with the extra instance.

## Relation to the published premise

`UnequalSemilocalFactorizationStatement` implies this statement: specialize it to
totally complex `F`. No converse is claimed. The totally complex chain needs only this
statement, which is the weaker of the two premises.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3):

* proof of Theorem 4.1, printed pp.219–220: the factorization and the cancellation of the
  central signs;
* §3.2, printed pp.216–217: the archimedean factors and the archimedean functional
  equation (Theorems 3.5 and 3.6).

## Provenance

Internal intermediate result toward the semi-local functional equation of the unequal-rank
partial Rankin–Selberg integrals. It belongs to the form of the global chain that is
restricted to totally complex base fields. The form, with the instance inserted after
`[NumberField F]` and the rest verbatim, is the one used for the TC forms of
published statements.
