# Preservation of analytic temperedness by normalized GL induction

`Langlands.GLTemperedInductionPreservationStatement.{uF,uV}` is a closed
proposition definition. It isolates exactly the final conclusion of the
published `Langlands.GLTemperedInductionStatement`, retaining its entire input
telescope. This module states preservation of analytic temperedness; it does
not prove it. The parent's input-unitarity and algebraic complete-reducibility
conclusions remain separate proof obligations. There is no irreducibility
conclusion for the induced representation.

## Exact statement and actual constructions

Quantify over every prime `p` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, and every supplied `T : F.TopologicalData`. With
`T.topology`, quantify over every positive total rank `n`, every ordered
positive block shape `B : GeneralLinear.BlockShape n`, and put

```text
M = B.Levi F.Carrier,
Q = M / Subgroup.center M.
```

Quantify over every measurable-space realization on this actual full-center
quotient with `BorelSpace`, every supplied Haar measure `μ` on it, every
`V : Type uV` with `AddCommGroup V` and `Module ℂ V`, and every actual
`σ : Representation ℂ M V`. The two hypotheses and conclusion are exactly

```text
Representation.IsIrreducible σ →
IsTemperedModCenter σ μ →
T.IsTempered (T.normalizedParabolicInduced B σ).
```

The field and carrier universes `uF` and `uV` are independent. The input carrier
is unrestricted apart from its displayed algebraic structures. The actual
induced function space has the universe required by its construction; the
statement imposes no equality between that universe and `uV`. The one-block
case is included. No tensor factorization, positive form, finite length, or
unitarity of `σ` is assumed.

`IsTemperedModCenter σ μ` includes admissibility and a smooth unitary scalar
character of the full Levi center. For every vector, every element of the
actual smooth contragredient, and every real `ε > 0`, the descended coefficient
norm belongs to `L^(2+ε)(Q, μ)`. Admissibility supplies smoothness and
finite-dimensional compact-open fixed spaces; it does not impose
finite-dimensionality of `V`.

The input hypothesis concerns the single supplied `μ`. It does not require
input temperedness for all Levi Haar measures as an extra premise. The
conclusion invokes the existing `T.IsTempered`, which quantifies over every
Borel Haar measure on the ambient quotient `GL_n(F) / Z(GL_n(F))`.
The imported helpers
`T.exists_isHaarMeasure_leviCentralQuotient` and
`T.exists_isHaarMeasure_centralQuotient` provide actual Borel Haar measures,
so these quantifications are nonvacuous.

The imported `T.normalizedParabolicInduced B σ` is smooth induction from the
actual standard upper block parabolic `P_B`. It has covariance and action

```text
f(m u g) = δ_(P_B)(m)^(1/2) σ(m) f(g),
(i_(P_B)^G σ)(g₀) f(g) = f(g g₀).
```

The square root is positive. For block ranks `n_i = B.size i`, the actual
modulus is

```text
δ_(P_B)(m) = ∏_(i<j) |det m_i|^(n_j) / |det m_j|^(n_i),
```

with the residue-normalized absolute value `q^(-ord_F)`. Neither the
parabolic, the normalization, nor the right-translation action is changed.
No imported Lean or Markdown pair is modified.

## Original source and the focused derivation

The registered original is A. J. Silberger, *Introduction to Harmonic Analysis
on Reductive p-adic Groups* (1979), source
`silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The retained file is
`/home/taskhub/central-library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`.

Lemma 4.5.15, printed p.191 (one-based PDF p.197), states complete
reducibility and temperedness of `Ind_P^G(δ_P^(1/2) σ)` for an irreducible
admissible tempered representation of the Levi. The notation for these input
representations is fixed on p.190 (PDF p.196). Both pages were read and their
formulas checked visually for this contribution; the retained hash was
rechecked. No source-specific errata file was found in the supplied Library
notes or project notes on 2026-10-25.

The provenance is derived: specialize the source to `GL_n(F)` and its actual
standard block Levi, retain only the temperedness conclusion, and use the
analytic convention correspondence documented in the complete published
[TemperedInductionStatement](TemperedInductionStatement.md). The broader
reductive-group scope and the complete-reducibility conclusion are not
additional assertions of this new proposition.

The source proof first obtains complete reducibility from unitarity, citing
Corollary 4.5.13. For temperedness it then uses precisely:

1. Lemma 4.5.2, the character criterion for temperedness. Its converse is used
   after complete reducibility has been established.
2. Theorem 1.13.2, the induced-character formula, identifying the induced
   character evaluated on a compactly supported test function with the Levi
   character evaluated on the normalized constant term of its
   `K`-conjugation average.
3. Theorem 4.4.3, continuity of the constant-term map on the relevant Schwartz
   spaces. Together with the tempered Levi character, it gives a continuous
   extension of the induced character.

Following this route requires actual definitions of the relevant test-function
and Schwartz spaces, their topologies, characters as distributions,
conjugation averaging, and normalized constant terms, together with proofs of
these three results and the complete-reducibility input needed by the
criterion. Their appearances in the source are dependency locators, not
implemented Lean theorems. Substantial missing definitions, statements and
proofs must be isolated in focused prerequisites before using them. This
statement adds no theorem-valued fields to stand in for those facts.

## Analytic boundary and an alternative proof route

The complete analytic-convention explanation in the imported parent's Markdown
was read for this contribution. Silberger's tempered functions use weak
`Ξ`-polynomial bounds and Schwartz distributions. Those notions are not
definitionally the Library's `L^(2+ε)` predicate. The parent's documented
translation and its Waldspurger source locators remain mathematical proof
obligations, including:

- identifying the actual full-center quotients and product-Levi topology
  with the split-center quotients used in the estimates, without factoring
  the arbitrary representation `σ`;
- comparing the actual smooth-dual coefficients with the source coefficient
  conventions, proving their descent and measurability, and obtaining the
  required weak-bound/integrability implications using actual Cartan volumes,
  `Ξ` bounds and Jacquet asymptotics;
- constructing the induced smooth unitary scalar central character from the
  input character: ambient scalar matrices give diagonal Levi scalars, on
  which the block modulus is one;
- proving the Haar uniqueness and positive finite rescaling statements and
  invariance of finite-exponent `MemLp` membership, so one input Levi Haar
  measure suffices and every ambient Haar measure is covered.

This list records what a proof must establish; no analytic bridge is a new
hypothesis or a theorem proved here.

A proof by the geometric lemma and normalized Jacquet exponents is also
possible in scope, but requires the actual structural and analytic theorems.
The existing `Langlands.GLTemperedExponentCriterionStatement` compares
`T.IsTempered` with weak bounds for exponents of normalized upper standard
Jacquet modules on the monotone block-absolute-value chamber. Its exact proof
task is `c98c74eb-a4cb-4924-8df8-f7556ca47689`, owned by Worker 349; that owner
was contacted for coordination. This statement is not a proved implication,
and its `GL_n` formulation alone does not supply the needed arbitrary-Levi
analytic comparison. Reuse its eventual accepted proof and coordinate any
additional Levi or geometric-lemma prerequisites rather than duplicating or
assuming them.

The proof successor must retain this exact analytic target. Downstream
tempered exhaustion, tempered unitarity and genericity, square-integrable
block induction, or regular Langlands classification cannot discharge this
upstream prerequisite. Independent acceptance and publication of the present
statement establish its formulation only.
