# Existence of epsilon factors of arbitrary irreducible pairs

Author: Worker 1411. This module, in namespace `Langlands.RankinSelberg`,
defines the proposition `LanglandsPairEpsilonFactorExistenceStatement`. It
asserts that every pair of irreducible admissible smooth representations of
positive-rank p-adic general linear groups has an actual epsilon factor
`e : ℂˣ × ℤ`, certified by the published relation `IsLanglandsPairEpsilonFactor`
of the module `LanglandsFactors`. The module also proves a conditional
reduction theorem, `langlandsPairEpsilonFactorExistence_of_classification`,
which derives the statement from classification, exhaustion and block-factor
existence inputs. The statement itself is not proved.

## The statement

`LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}` quantifies over:

- every prime `p` and every `F : PadicField.{uF} p`, with its canonical
  topological data;
- every `ψ : UnitaryAdditiveCharacter F.Carrier`;
- every `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`;
- all `r t : ℕ`;
- every `π : SmoothRep.{0, uF, max uF uV} ℂ (GL_(r+1)(F))` and every
  `σ : SmoothRep.{0, uF, max uF uW} ℂ (GL_(t+1)(F))`.

Its hypotheses are exactly `Representation.IsIrreducible` and
`SmoothRep.IsAdmissible` for `π` and for `σ`. Its conclusion is

`∃ e : ℂˣ × ℤ, IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν.val π σ e`.

There is no hypothesis of unitarity or genericity, no chosen Langlands datum,
and no factor certificate or existence input. The ranks `r + 1` and `t + 1`
are arbitrary positive integers, in either order.

## Meaning of the certificate

The relation is the published one; this module does not change it.
`IsLanglandsPairEpsilonFactor F ψ ν π σ e` is the conjunction of:

1. some `SquareIntegrableLanglandsDatum` `d` of rank `r + 1` has
   `d.IsLanglandsQuotient π`;
2. some such datum `d'` of rank `t + 1` has `d'.IsLanglandsQuotient σ`;
3. for *every* pair of such data, `IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e`.
   This says there is a family `b i j` of block epsilon factors with
   `IsPadicRankEpsilonFactor F ψ ν τ_i μ_j (b i j)` for all blocks `τ_i` of
   `d` and `μ_j` of `d'`, and `e = epsilonFactorProduct b`.

A `SquareIntegrableLanglandsDatum` is an ordered block shape with irreducible
essentially square-integrable blocks `τ_i` and real exponents `α(τ_i)`, where
`ν^(-α(τ_i)) τ_i` carries an invariant positive definite form and
`α(τ_1) ≥ ⋯ ≥ α(τ_p)`. `IsLanglandsQuotient π` says that `π` is irreducible
and is a quotient of the normalized induction `i(τ_1, …, τ_p)` from the
standard upper block parabolic subgroup.

So the statement asserts three things for each pair:

- both representations are Langlands quotients of square-integrable data;
- every block pair of every presenting datum pair has a JPSS epsilon factor;
- the products of these factors do not depend on the presenting data.

`IsLanglandsPairEpsilonFactor.unique` already shows that `e` is unique.

## Normalization

- **Monomial.** `e = (c, m)` represents `ε(s, π × σ, ψ) = c q^(-ms)`, where
  `q` is the residue cardinality of `F.canonicalTopologicalData`.
  `epsilonFactorProduct b` is `(∏_i ∏_j (b i j).1, ∑_i ∑_j (b i j).2)`, with
  complex coefficients multiplied and integer exponents added.
  `epsilonMonomial_factorProduct` proves that this pair evaluates to the
  product of the block monomials.
- **Blocks.** `IsPadicRankEpsilonFactor` is `IsPadicSymmetricEpsilonFactor` at
  positive block ranks. It is `False` if a rank is zero, which never happens
  for actual blocks. `IsPadicSymmetricEpsilonFactor` reads the pair with the
  larger rank first; equal ranks keep the given order. For equal ranks the
  Library proves the exchange of `IsPadicPairEpsilonFactor` for
  representations of Whittaker type and a self-dual Haar measure
  (`Langlands.RankinSelberg.equalRankFunctionalEquationSwap`, JPSS (2.12));
  this module does not use it. It unfolds through
  `IsPadicPairEpsilonFactor`, which uses the canonical `q` and normalized
  absolute value of `F`, to `IsPairEpsilonFactor`. That relation asks for
  nonzero Whittaker functionals of both representations, with `ψ` for the
  larger rank and `ψ⁻¹` for the other. For every compatible quotient measure
  and all nonzero such functionals, it asks for the JPSS local functional
  equation with the monomial `c q^(-ms)`.
- **Character and measure.** The same `ψ` and `ν` are used for every block
  pair. `ψ` is nontrivial by its type: `UnitaryAdditiveCharacter` bundles
  continuity, unit-circle values and `toAddChar ≠ 1`. `ν` ranges over the
  published subtype `SelfDualHaar` of Haar measures self-dual for `ψ`, and
  `ν.val` is passed to the relation. This is the same normalization as
  `LanglandsPairLFactorExistenceStatement`. The relation accepts any additive
  Haar measure, so self-duality is a restriction on the claim, not a change of
  the relation. The statement does not assert that a self-dual measure exists.

## Source audit

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983). Registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page = PDF page + 365. Read from the page images.

- **(9.4), printed page 458 (PDF page 93).**
  - `ξ = Ind(π_1, …, π_m)` with `π_i = π_(i,0) ⊗ α^(u_i)`, the `π_(i,0)`
    tempered and `u_1 > ⋯ > u_m`; `η` is built in the same way.
  - The Proposition, display (3): `L(s, ξ × η)` is the product of the
    `L(s, π_i × σ_j)`.
  - An irreducible admissible `π` is uniquely a quotient of a representation
    of Langlands' type. If `π` is generic it has the same Whittaker model as
    `ξ`, which gives display (4): `L(s, ξ × η) = L(s, π × σ)`.
  - "In any case one can take (4) as a definition of `L(s, π × σ)` for any
    pair `π, σ` of irreducible, admissible representations."
- **(9.5), printed pages 462-463.** The classification `λ ↦ π[λ]` and the
  biadditivity of `L(s, π × σ)` under `⊞`.
- **Introduction (0.1), displays (15)-(16), printed pages 371-372 (PDF
  pages 6-7).** Following Gelfand and Kazhdan, the authors suggest adding
  `ε_v(s, ρ ⊗ η, ψ) = ε_v(s, l_r(ρ) × l_t(η))` for all `ρ, η` to the list of
  axioms expected of a conjectural correspondence `l_r`. This presupposes
  local epsilon factors of arbitrary pairs, but it neither defines them nor
  asserts that they exist.

The two passages (9.4) and (9.5) concern only the L-factor. Neither defines or states an epsilon
factor of a nongeneric pair. The epsilon conclusion of this module is
therefore not attributed to JPSS. From JPSS it takes only the wording
"irreducible, admissible" for the class of pairs, and the block relation
(the analytic epsilon factor of a generic pair).

G. Henniart, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587-602. Registered source
`henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
Read from the text layer.

- **§2.8, printed page 596 (PDF page 10, zero-based index 9).** This is the
  source of the epsilon statement.
  - `A_2` is the set of classes of essentially square-integrable
    representations. Each element is uniquely `ν^(α(π)) π_u` with `π_u`
    unitary and `α(π)` real.
  - If `α(π_1) ≥ ⋯ ≥ α(π_r)`, condition (*), then `i(π_1, …, π_r)` has a
    unique irreducible quotient `J(π_1, …, π_r)`. Its class does not depend
    on the order, provided (*) holds.
  - This gives a bijection from `N[A_2] − {0}` onto the set `A` of all
    irreducible classes. Henniart refers to [1] and [6, Intr.]; [6] is JPSS
    1983.
  - For `π = ∑_(i∈I) π_i` and `π' = ∑_(j∈J) π'_j`, the final display gives
    `L(s, π × π') = ∏_(i,j) L(s, π_i × π'_j)`,
    `γ(s, π × π') = ∏_(i,j) γ(s, π_i × π'_j, ψ)` and
    `ε(s, π × π') = ∏_(i,j) ε(s, π_i × π'_j, ψ)`.

    The left sides omit `ψ`, but the same `ψ` occurs in every factor.
- **§2.6, printed page 595.** The `γ` factors of Steinberg-type
  representations are products of block factors because `γ` is
  multiplicative for normalized induction. Henniart remarks that this also
  controls the `ε` factors.
- **§2.5, printed page 594.** `i(π_1, …, π_r)` is normalized induction from
  the parabolic subgroup of block upper triangular matrices.

How the statement matches §2.8:

- **Quotients.** `SquareIntegrableLanglandsDatum` is Henniart's ordered
  family satisfying (*), with exponents `α`. `IsLanglandsQuotient` is his
  irreducible quotient `J` of `i(π_1, …, π_r)`, with the same upper
  parabolic.
- **Every presentation.** The certificate quantifies over every presenting
  datum, not a chosen one. Henniart's bijection and order independence make
  the presentation unique up to permutation and isomorphism of blocks. The
  published `langlandsPairEpsilonDataIndependence_of_classification` proves
  that such data give equal products. Hence Henniart's product satisfies the
  certificate, and by uniqueness the certificate determines it.
- **The product formula.** The certificate's value is `∏_(i,j)` of the block
  factors, as in the display.
- **Henniart's ε as a definition.** For a nongeneric pair Henniart gives no
  other definition of `ε`: the display plays the same role for `ε` that
  JPSS's (4) plays for `L`. Existence of this factor thus amounts to three
  facts: the classification, the existence of the block factors, and order
  independence. These are the contents of the certificate.
- **Block factors.** Henniart's `ε(s, π_i × π'_j, ψ)` is the JPSS epsilon
  factor of a generic pair. Essentially square-integrable representations
  are generic. The Library states the unitary square-integrable case as the
  proposition `Langlands.Classification.SquareIntegrableGenericity`; this
  module does not use it. The block relation is the
  Library's JPSS functional-equation relation, which includes the existence
  of nonzero Whittaker functionals.
- **Generic pairs.** For generic `π, σ` Henniart's product also equals the
  analytic JPSS factor of `(π, σ)`. That compatibility is a theorem, not part
  of the definition, and it is not stated here.

The registered project notes record no erratum for either source.

## Relation to existing Library statements

- **Nongeneric L-factor existence.**
  `LanglandsPairLFactorExistenceStatement` in
  `LanglandsQuotientLFactorStatement` has the same binders and the same
  irreducible and admissible hypotheses.
  - Its factor is JPSS's definition (4): the L-polynomial of the standard
    modules of tempered Langlands data.
  - This statement's factor is Henniart's product over square-integrable data.
  - Neither statement implies the other, and no relation between the two
    factors is asserted. Gamma factors are not stated here either.
  - `LanglandsPairGammaInput` in `LanglandsGammaFactor` asks for both
    existences, together with the dual L-factor.
- **Classification and exhaustion.** `SquareIntegrableLanglandsExhaustion`
  (an irreducible representation has a square-integrable Langlands head) and
  `SquareIntegrableLanglandsClassification` (isomorphic quotients have matching
  blocks) are published propositions of
  `Classification/MultisegmentClassificationStatement`. They are not
  hypotheses of this statement; a proof of the statement must supply them.
- **Block-factor existence.** The existence of an epsilon factor for each pair
  of essentially square-integrable blocks is the analytic part. It is
  JPSS's local functional equation (Theorem 2.7(iii), printed page 391, as
  cited in `EpsilonFactor`) together with the genericity of the blocks. It is not a hypothesis here.
- **Constructor.** `langlandsPairEpsilonFactorOfClassification` in
  `LanglandsFactorDescent` takes these inputs and returns an actual pair with
  this certificate, deriving datum independence from classification. The
  reduction theorem below uses it, and no constructor is duplicated.

## Universes

- **Independent universes.** The field universe `uF` and the two carrier
  parameters `uV`, `uW` are independent. The representations have the
  carrier shape of the published L-existence statement: `max uF uV` and
  `max uF uW`.
- **Saturated certificate.** The certificate is instantiated at
  `.{uF, max uF uV, max uF uW}`, so the blocks of the Langlands data live in
  the carrier universes of `π` and `σ`. This is the exact output type of
  `langlandsPairEpsilonFactorOfClassification`. The published classification
  and exhaustion propositions quantify over blocks at these universes.
- **What is not claimed.** The unsaturated instance `.{uF, uV, uW}` would
  also assert that the Langlands data of `π` can be realized with blocks in
  the possibly smaller universe `uV`. That needs a universe-lowering argument
  and is not claimed. No unequal universes are identified.
- **Comparison with the L-statement.** This statement at `.{uF, uV, uW}` is
  the instance at `.{uF, max uF uV, max uF uW}` of the analogous unsaturated
  formulation. `max uF (max uF uV)` and `max uF uV` are the same level, so
  the binders are unchanged.
- **Common universe.** At `uV = uW = uF = u` the certificate is
  `IsLanglandsPairEpsilonFactor.{u, u, u}`, the instance used by single-universe
  consumers.

## Hypotheses

- **Irreducible and admissible.** These are JPSS's "irreducible, admissible"
  and the hypotheses of the L-existence statement.
- **Admissibility is redundant.** Exhaustion needs only irreducibility, so
  the reduction theorem does not use admissibility. Irreducible smooth
  representations of `GL_n(F)` are admissible (Jacquet; Bernstein), so the
  hypothesis does not narrow the class of pairs. The Library proves this as
  `Langlands.Classification.TwoFactorCommutativity.isAdmissible_of_isIrreducible`
  in `Classification/TwoFactorProductConstituentCommutativityProof`. That
  theorem is the admissibility component of the published
  `Langlands.CuspidalSupport.cuspidalEmbedding`. It holds for any topological
  data of `F`, in particular `F.canonicalTopologicalData`, and for any carrier
  universe, so it covers both `π` and `σ`. The hypotheses are kept to match
  the source wording and the L-existence statement.
- **Field.** `F` is a p-adic field (`PadicField`), as in the other JPSS units,
  because the reused certificate `IsLanglandsPairEpsilonFactor` and the
  canonical topological data `F.canonicalTopologicalData` are stated for
  `PadicField`.

## The reduction theorem

`langlandsPairEpsilonFactorExistence_of_classification` proves
`LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}` from three
hypotheses:

1. `hex`: for every `p` and `F`, `SquareIntegrableLanglandsExhaustion` at
   `.{uF, uV}` and at `.{uF, uW}`;
2. `hcl`: for every `p` and `F`, `SquareIntegrableLanglandsClassification` at
   `.{uF, uV}` and at `.{uF, uW}`;
3. `hb`: for every `p`, `F`, `ψ`, `ν : SelfDualHaar`, `r`, `t`, and all
   square-integrable data `d` of rank `r + 1` (blocks in `max uF uV`) and
   `d'` of rank `t + 1` (blocks in `max uF uW`),
   `SquareIntegrableDataEpsilonExistence F ψ ν.val d d'`.

The proof introduces the binders and applies
`langlandsPairEpsilonFactorOfClassification` with the irreducibility
hypotheses, the two exhaustion and two classification instances, and the
block input restricted to presenting data. It returns the property of the
constructed subtype. Input `hb` covers all data, not only presenting data,
which is the natural form of the analytic block existence.

The theorem records that these three inputs, and no others, are the proof
dependencies of the statement. None of them is proved here, and they are not
hypotheses of the statement itself.

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.LanglandsPairEpsilonFactorExistenceStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.

The same check with declaration
`Langlands.RankinSelberg.langlandsPairEpsilonFactorExistence_of_classification`
reports a theorem with the same three axioms.
