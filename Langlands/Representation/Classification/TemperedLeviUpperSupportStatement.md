# Upper discrete-series quotient support of tempered product-Levi representations

Author: Worker 276.

`Langlands.GLTemperedLeviUpperSupportStatement.{uF,uV}` is a closed
proposition definition. It isolates the middle-to-coarse support clause of
the published host target `Langlands.GLTemperedJointSupportStatement`. This
module supplies the statement only. It proves no support, analytic, or
induction assertion, and it does not change the host target or any imported
pair.

## Quantifiers and analytic input

For every prime `p` with `Fact p.Prime`, field `F : PadicField.{uF} p`,
compatible realization `T : F.TopologicalData`, positive natural rank `n`,
ordered block shape `B : GeneralLinear.BlockShape n`, and actual complex
representation `π : Rep.{uV} ℂ (B.Levi F.Carrier)`, the only representation
hypotheses are `Representation.IsIrreducible π.ρ` and
`RelativeRegularComparison.IsLeviTempered T B π`.

Here `B.Levi F.Carrier` is the product of the general linear groups of the
block sizes of `B`. The topology is the one supplied by `T`. The analytic
hypothesis uses the actual quotient

`B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)`

by the full center of the product Levi, not only the diagonal scalars of
`GL_n`. It quantifies over every measurable structure making that quotient a
Borel space and every Haar measure on it. For each such measure,
`IsTemperedModCenter` requires admissibility (which includes smoothness) and
a smooth unitary scalar central character. Every absolute matrix coefficient,
formed from a smooth-dual functional and any vector and descended to the
quotient, must lie in `L^(2+ε)` for every positive real `ε`.

No tensor presentation, chosen central character, selected support, critical
pair, opposite embedding, unitarizability, or quotient map is an input. No
classification, relative recovery, or head result is a premise, and neither
is the host joint-support statement.

## Conclusion

The conclusion chooses a refinement `Q : Geometric.BlockRefinement B` and,
with `D := B.flatten Q`, a representation

`σ : Rep.{max uF uV} ℂ (D.Levi F.Carrier)`

such that:

- `Representation.IsIrreducible σ.ρ`;
- `RelativeRegularComparison.IsLeviSquareIntegrable T D σ`;
- there is a complex-linear intertwiner
  `q : (RelativeRegularComparison.middleInduced T B Q σ).ρ.IntertwiningMap π.ρ`
  with `Function.Surjective q`.

Square-integrability uses the same convention on the quotient of
`D.Levi F.Carrier` by its full center: for every Borel Haar measure it
requires admissibility, a smooth unitary scalar central character, and `L²`
integrability of every descended absolute matrix coefficient.

Unrefined blocks are allowed, so a refinement may leave every block of `B`
whole, as when `π` is itself square-integrable. The conclusion asserts
existence only. It gives no uniqueness of `Q` or `σ`,
no section of `q`, and no fine cuspidal data.

## Induction and normalization

`middleInduced T B Q σ` first pulls `σ` back along the inverse of the
constructed equivalence `flattenedLeviEquiv F.Carrier B Q`. That equivalence
identifies `D.Levi F.Carrier` with the actual subgroup
`refinedLevi F.Carrier B Q` of `B.Levi F.Carrier` by nested block-diagonal
matrices. It then applies `RelativeJacquetMultiplicity.innerInduced T B Q`,
the untwisted `T.normalizedRefinedInduced`. This inflates along the actual
Levi projection of the upper product parabolic
`refinedParabolic F.Carrier B Q`, imposes covariance by the positive half
power of its modulus, and lets `B.Levi F.Carrier` act by right translation on
smooth induced functions. Absolute values are residue-normalized as
`q^(-valuation)`. No real twist is applied to `σ`.

## Carrier universes

The field universe `uF` and the input carrier universe `uV` are independent.
The original coarse carrier stays in `Type uV`. The support carrier is allowed
in `Type (max uF uV)`, because a support representation may be constructed
from induced or Jacquet carriers. Such carriers involve functions on, or
coinvariants for, groups of matrices over `F.Carrier`. Normalized induction
from `Type (max uF uV)` again has carrier universe `max uF uV`. The quotient
map therefore runs between distinct universes; no equality of field and
carrier universes is imposed.

## Original passages and derivation

The direct source is A. J. Silberger, *The Langlands Quotient Theorem for
p-adic Groups*, Math. Ann. 236 (1978), 95–104 (S78). It is retained as
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
On printed p.99, the proof of Proposition 5.1 fixes nested p-pairs
`(P'',A'') ≻ (P',A') ≻ (P,A)`, with `σ''` in a tempered class for `M''`. It
then uses Silberger (1979), Corollary 4.5.11, to assume that there is a
discrete-series `σ'` of `M'` such that `σ''` occurs as a quotient of
`I(P' ∩ M'', σ')`. The fine cuspidal step follows and is outside this
statement.

On p.96, S78 fixes `I(P,σ) = Ind_P^G(δ_P^{1/2} σ)`. On p.97 it recalls that
Jacquet functors and normalized induction are exact and transitive. The same
page says that, by S79 Theorem 3.3.1 and an easy induction, an irreducible
admissible `π` occurs as a subrepresentation of `I(P,σ)` if and only if it
occurs as a quotient of `I(P̄,σ)`, for irreducible admissible `σ`. On p.98,
S78 notes that every irreducible tempered representation is a direct summand
of some `I(P,ω)` with `ω` in the discrete series of `M`. Worker 276 read
pp.96–99 and checked pp.97 and 99 as images.

The cited corollary is in A. J. Silberger, *Introduction to Harmonic Analysis
on Reductive p-adic Groups* (1979) (S79), registered as
`silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`, retained at
`/home/taskhub/central-library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`.
Corollary 4.5.11, pp.189–190, concerns an irreducible admissible tempered
representation `π` of the ambient reductive group. It produces a standard
p-pair `(P,A)` and a discrete-series `σ` of `M` with an embedding of `π` into
`Ind_{P̄}^G(δ_{P̄}^{1/2} σ)`, the normalized induction from the opposite
parabolic. Its proof uses Corollaries 4.5.7 and 4.5.9, Theorem 4.5.10, and
Theorem 3.2.4, arguing as in Corollary 2.4.2. By Corollary 4.5.13, p.190,
such a `π` is unitary. Corollary 4.5.14, p.190, uses this to show that its
weak exponents along opposite p-pairs `(P,A)` and `(P̄,A)` agree. Worker 276
read pp.189–190 and checked them as images. No erratum specific to
these passages of S78 or S79 was found in the project's literature index.

The present target is a derived product-Levi specialization of the S78
setup, not a literal statement of either source. S78 states the conclusion
with its own normalized induction, and S79 gives an opposite embedding in an
ambient group. Neither source states the exact Lean quotient formula, with
actual standard block parabolics of a product Levi, the flattened-Levi
identification, the residue-normalized modulus, and the analytic predicates
above.

## Retained proof obligations

A proof must supply at least the following, without assuming any of them.

1. **Product-Levi support.** S79 Corollary 4.5.11 concerns one reductive
   group. A proof can redo the Jacquet-module and exponent analysis directly
   for the product Levi. Alternatively it can factor `π` into blocks and use
   the ambient statements. A factorization route needs analytic tensor
   equivalences for temperedness and square-integrability on the full central
   quotients, and must recover the original representation. Published
   admissible product-Levi factorization alone proves neither analytic
   equivalence.
2. **Analytic comparison.** The predicates quantify over all Borel Haar
   measures on full-center quotients. They must be compared with the source's
   tempered and discrete-series conditions, including measure compatibility
   and the coefficient and exponent criteria.
3. **Opposite to upper, and embedding to quotient.** The source yields an
   opposite-induction embedding, while the target needs an upper-induction
   quotient. S78 bridges this with the p.97 subrepresentation/opposite
   quotient correspondence from S79 Theorem 3.3.1, which is not available
   here for the actual Lean inductions. A proof may establish that
   correspondence, or use unitarity and S79 Corollary 4.5.14,
   direct-summand or semisimplicity results, or smooth duality with
   admissible biduality. It must also handle block reversal or parabolic
   conjugation with the correct modulus factors. The dual inputs must keep
   irreducibility and the analytic properties.
4. **Identification of support.** The Levi produced must be identified with
   `(B.flatten Q).Levi F.Carrier` through `flattenedLeviEquiv`, and the
   induction with `middleInduced`. The intertwiner must be constructed
   across the carrier universes above.

The [scope audit](../../../notes/jacquet/silberger-lemma53-scope.md) on S78
Lemma 5.3 is preserved: this statement and its eventual proof supply no
unrestricted multiplicity comparison. A proof must not use the downstream
square-integrable Langlands classification or regular-data uniqueness.

## Relation to existing work

The host `GLTemperedJointSupportStatement` asserts, for the same `π`, a
middle-to-coarse quotient together with fine support and a fine-to-coarse
quotient. Its first clause, after the obvious projection, is this
statement. This target is weaker, so it can be proved separately and then
combined with fine support and induction in stages.

The Library also has ambient `GL_n` statements in
`Langlands.Representation.Classification.TemperedSupportStatement`.
`GLTemperedDiscreteSeriesSupportStatement` concludes an opposite embedding
for an irreducible tempered representation of `GL_n`. The summand and
same-σ opposite-to-upper statements compare opposite and upper inductions for
a given discrete-series `σ`. They concern `GL_n` rather than an arbitrary
product Levi, and conclude no upper refined quotient for product-Levi input.
Their tasks, the analytic block tensor tasks, the discrete-series
positive-root support task, product-Levi tempered unitarity, and normalized
nested induction keep their own scopes. This module neither duplicates their
targets nor assumes their conclusions.
